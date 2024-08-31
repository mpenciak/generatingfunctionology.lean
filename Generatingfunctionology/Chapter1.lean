import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown

noncomputable section

open PowerSeries

variable {R : Type*}
#check R⟦X⟧

abbrev α : ℕ → ℚ
| n + 1 => 2 * (α n) + 1
| 0 => 0

def shift_left (α : ℕ → ℚ) : ℕ → ℚ := fun n => α <| n + 1

def shift_k (α : ℕ → ℚ) (k : ℕ) : ℕ → ℚ := fun n => α <| n + k

abbrev f := invUnitsSub (R := ℚ) 1

def shifted_f := X * f

def f_coeff_eq_one : coeff ℚ 0 f = 1 := by
  simp only [coeff_zero_eq_constantCoeff]
  rw [constantCoeff_invUnitsSub]
  exact divp_one 1

#check coeff_mul_X_pow

def shift_1_eq_mul_X (α : ℕ → ℚ) : X * mk (shift_left α) + C ℚ (constantCoeff ℚ (mk α))= mk α := by
  ext n
  simp [shift_left]
  rw [← coeff_mul_X_pow (n := 1)]
  rw [pow_one]
  match n with
    | 0 => simp?
    | k + 1 => simp [shift_left]

-- A(x)
def A : ℚ⟦X⟧ := mk α

abbrev one_minus_2X := invUnitsSub (R := ℚ) (Units.mkOfMulEqOne (1/2) 2 (by rfl)

lemma A_eq_1 : A = X * (2 * A + invUnitsSub 1) := sorry

#check Units

#check coeff_C

lemma helpful_lemma : (C ℚ 1 - 2 * X) * one_minus_2X = C ℚ 2 := by
  ext n
  match n with
    | 0 =>
      simp
    | k + 1 =>
      conv_rhs =>
        rw [coeff_C]
        simp
      have : ((C ℚ) (Units.mkOfMulEqOne (1/2 : ℚ) 2 (by rfl)) - X) * one_minus_2X = 1 := by rw [mul_comm, one_minus_2X, invUnitsSub_mul_sub]


#check invUnitsSub_mul_sub

lemma A_eq_2 : A = X * (invUnitsSub 1) * one_minus_2X := by



abbrev F₁ : ℚ⟦X⟧ := 2 * (1 - X)⁻¹
abbrev F₂ : ℚ⟦X⟧ := 1 * (1 - 2*X)⁻¹

lemma A_frac : X * (1 - X)⁻¹ * (1 - 2 * X)⁻¹ = X * (F₁ - F₂) := sorry

lemma α_eq (n : ℕ) : α n = 2 ^ n - 1 := sorry

#check A
