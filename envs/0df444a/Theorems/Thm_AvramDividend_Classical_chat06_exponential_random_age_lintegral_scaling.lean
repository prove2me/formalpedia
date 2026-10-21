-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_exponential_random_age_lintegral_scaling
-- name    : AvramDividend.Classical.chat06_exponential_random_age_lintegral_scaling
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:15:14.285706+00:00
-- url     : https://prove2.me/theorems/ae6e5419-7ae1-4fd9-898c-9845673d8a0a
-- title:
--   Exponential survival kernel scaling under arbitrary nonnegative age laws
-- statement:
--   For any finite or infinite nonnegative-age law, the lintegral of the exponential waiting-time survival kernel at age plus t factorises as the original age-integrated tail multiplied by exp(-t), provided ages are almost surely nonnegative. This is a Tonelli-compatible exact analytic step for unrestricted continuous random-age memorylessness and makes no finite-support assumption.
-- source:
--   Remote Lean private verified source bv_exp_tail_random_age_lintegral_scaling_chat06_20261020.lean pinned 0df444a360eaa60ab8c11dca51a86af692955474 job 243d9649-5d0c-492d-8c2e-b8b331ad9bfc.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_exponential_random_age_lintegral_scaling
    (μ ν : Measure ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hAge : ∀ᵐ a ∂μ, 0 ≤ a)
    (hTail : ∀ u : ℝ, 0 ≤ u →
       ν (Ioi u) = ENNReal.ofReal (Real.exp (-u))) :
    (∫⁻ a, ν (Ioi (a + t)) ∂μ) =
      (∫⁻ a, ν (Ioi a) ∂μ) *
        ENNReal.ofReal (Real.exp (-t)) := by sorry
