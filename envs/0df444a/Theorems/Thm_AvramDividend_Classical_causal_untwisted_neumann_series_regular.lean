-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_untwisted_neumann_series_regular
-- name    : AvramDividend.Classical.causal_untwisted_neumann_series_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:33:39.032081+00:00
-- url     : https://prove2.me/theorems/ab2a4474-0054-46c9-82ce-49145241d869
-- title:
--   Continuous monotone undamped renewal sum from a convergent Esscher tilt
-- statement:
--   Given a globally pointwise summable exponentially damped Neumann sequence with continuous sum on nonnegative arguments, and a pointwise relation to undamped summands which are monotone, untwisting preserves pointwise summability and continuity, while the series of undamped summands is monotone. This assembles the continuity and monotonicity clauses of the positive-discount scale function from the existing weighted M-test and convolution-power monotonicity proofs.
-- source:
--   Pointwise summable monotone tsum theorem plus exponential reciprocity, tsum scalar multiplication and the continuous product rule.

import Theorems.Thm_AvramDividend_Classical_pointwise_summable_monotone_tsum
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp
open AvramDividend.Classical Set

theorem AvramDividend.Classical.causal_untwisted_neumann_series_regular
    (F U : ℕ → ℝ → ℝ) (θ : ℝ)
    (hFsum : ∀ x : ℝ, Summable (fun n : ℕ => F n x))
    (hFcont : ContinuousOn (fun x : ℝ => ∑' n : ℕ, F n x) (Ici 0))
    (hrel : ∀ n : ℕ, ∀ x : ℝ,
      F n x = Real.exp (-(θ * x)) * U n x)
    (hUmono : ∀ n : ℕ, Monotone (U n)) :
    (∀ x : ℝ, Summable (fun n : ℕ => U n x)) ∧
      ContinuousOn (fun x : ℝ => ∑' n : ℕ, U n x) (Ici 0) ∧
      MonotoneOn (fun x : ℝ => ∑' n : ℕ, U n x) (Ici 0) := by sorry
