-- Prove2me | solution 1 for siegel_logdensity_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T19:05:16.822274+00:00
-- url     : https://prove2.me/submissions/f6521d72-45c2-40fc-a25a-f1393837a903

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open Set

theorem solution
    (lam K : ℝ) (p : ℕ) (mNat : ℕ) (t : ℝ)
    (hK : 0 < K)
    (hpos : 0 < 1 - Real.exp (-lam * t)) :
    Real.log (K * (1 - Real.exp (-lam * t)) ^ mNat * (Real.exp (-lam * t)) ^ p)
      = ((mNat : ℝ) * Real.log (1 - Real.exp (-lam * t)) - (p : ℝ) * (lam * t))
        + Real.log K := by
  have he : Real.exp (-lam * t) > 0 := Real.exp_pos _
  have h1 : Real.log (K * (1 - Real.exp (-lam * t)) ^ mNat * (Real.exp (-lam * t)) ^ p)
      = Real.log K + Real.log ((1 - Real.exp (-lam * t)) ^ mNat)
        + Real.log ((Real.exp (-lam * t)) ^ p) := by
    rw [Real.log_mul, Real.log_mul (ne_of_gt hK)]
    · positivity
    · exact ne_of_gt (mul_pos hK (by positivity))
    · positivity
  rw [h1]
  rw [Real.log_pow, Real.log_pow]
  have h2 : Real.log (Real.exp (-lam * t)) = -lam * t := Real.log_exp _
  rw [h2]
  ring
