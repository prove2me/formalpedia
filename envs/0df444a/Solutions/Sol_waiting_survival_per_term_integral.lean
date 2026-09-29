-- Prove2me | solution 1 for waiting_survival_per_term_integral
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T19:35:40.448938+00:00
-- url     : https://prove2.me/submissions/6439f4aa-a71b-426a-897e-d66253c822c3

import Theorems.Thm_exp_substitution_Ioi_to_Ioo
import Theorems.Thm_beta_nat_factorial
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

theorem solution (N k : ℕ) (lam : ℝ) (hlam : 0 < lam) (hk : k < N) :
    ∫ t in Ioi (0:ℝ), (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      = (1 / lam) * ((Nat.factorial k * Nat.factorial (N - k - 1) : ℝ) / Nat.factorial N) := by
  -- apply subst with g(u) = u^k (1-u)^{N-k-1} / lam
  have hkey := exp_substitution_Ioi_to_Ioo lam hlam (fun u => u ^ k * (1 - u) ^ (N - k - 1) / lam)
  -- LHS of hkey simplifies to our target integral
  have hL : (∫ t in Ioi (0:ℝ), |lam * Real.exp (-(lam * t))|
        * ((1 - Real.exp (-(lam * t))) ^ k * (1 - (1 - Real.exp (-(lam * t)))) ^ (N - k - 1) / lam))
      = ∫ t in Ioi (0:ℝ), (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only []
    have he : (0:ℝ) < Real.exp (-(lam * t)) := Real.exp_pos _
    have habs : |lam * Real.exp (-(lam * t))| = lam * Real.exp (-(lam * t)) := by
      rw [abs_of_pos]; positivity
    rw [habs]
    have h1q : (1 - (1 - Real.exp (-(lam * t)))) = Real.exp (-(lam * t)) := by ring
    rw [h1q]
    have hNk : N - k = (N - k - 1) + 1 := by omega
    rw [hNk, pow_succ]
    have hlne : lam ≠ 0 := ne_of_gt hlam
    field_simp
    rw [show N - k - 1 + 1 - 1 = N - k - 1 from by omega]
  rw [hL] at hkey
  rw [hkey]
  -- RHS: ∫_{Ioo 0 1} u^k (1-u)^{N-k-1}/lam  = (1/lam) ∫_{Ioo} u^k(1-u)^{N-k-1}
  have hR : (∫ u in Ioo (0:ℝ) 1, u ^ k * (1 - u) ^ (N - k - 1) / lam)
      = (1 / lam) * ∫ u in Ioo (0:ℝ) 1, u ^ k * (1 - u) ^ (N - k - 1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u _; ring
  rw [hR]
  -- convert Ioo to interval and apply beta_nat
  have hconv : (∫ u in Ioo (0:ℝ) 1, u ^ k * (1 - u) ^ (N - k - 1))
      = ∫ u in (0:ℝ)..1, u ^ k * (1 - u) ^ (N - k - 1) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  rw [hconv, beta_nat_factorial k (N - k - 1)]
  have hNeq : k + (N - k - 1) + 1 = N := by omega
  rw [hNeq]
