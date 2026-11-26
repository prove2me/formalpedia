-- Prove2me | solution 1 for section5_integer_matrix_bit_bound
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:51.20088+00:00
-- url     : https://prove2.me/submissions/b551b014-a06b-4367-9205-ce4097ab2788

import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Mathlib
import Theorems.Thm_section5_integer_matrix_product_bound
section
set_option autoImplicit false

/-! Explicit bit-growth bounds for the exact arithmetic in the power estimator. -/













theorem section5_integer_matrix_power_bound {n : ℕ} (A : Section5IntegerMatrix n)
    (B : ℤ) (hB : 0 ≤ B) (hA : A.Bounded B) (k : ℕ) :
    (A.power k).Bounded ((2*n*B)^k) := by
  induction k with
  | zero =>
    constructor
    · intro i j
      change |(1 : Matrix (Fin n) (Fin n) ℤ) i j| ≤ (2*n*B)^0
      by_cases h : i=j <;> simp [Matrix.one_apply,h]
    · intro i j
      change |(0:ℤ)| ≤ (2*n*B)^0
      norm_num
  | succ k ih =>
    have hh := section5_integer_matrix_product_bound (A.power k) A
      ((2*n*B)^k) B (pow_nonneg (by positivity) _) hB ih hA
    have hid : 2*(n:ℤ)*(2*n*B)^k*B=(2*n*B)^(k+1) := by rw [pow_succ]; ring
    simpa only [Section5IntegerMatrix.power,hid] using hh



end
set_option autoImplicit false
theorem solution {n : ℕ} (A : Section5IntegerMatrix n)
    (b c : ℕ) (hn : n ≤ 2^c) (hA : A.Bounded ((2:ℤ)^b)) (k : ℕ) :
    (A.power k).Bounded ((2:ℤ)^(k*(b+c+1))) := by
  have hh := section5_integer_matrix_power_bound A ((2:ℤ)^b) (by positivity) hA k
  have hn' : (n:ℤ) ≤ (2:ℤ)^c := by exact_mod_cast hn
  have hp : 2*(n:ℤ)*(2:ℤ)^b ≤ (2:ℤ)^(b+c+1) := by
    have hmul := mul_le_mul_of_nonneg_right hn' (by positivity : (0:ℤ) ≤ 2*2^b)
    rw [pow_add,pow_add]
    nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℤ) ≤ 2*n*2^b) hp k
  have heq : ((2:ℤ)^(b+c+1))^k=(2:ℤ)^(k*(b+c+1)) := by rw [← pow_mul,Nat.mul_comm]
  rw [heq] at hpow
  exact ⟨fun i j => (hh.1 i j).trans hpow,fun i j => (hh.2 i j).trans hpow⟩
