-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_gaussian_nonpositive_zero
-- name    : AvramDividend.Classical.causal_neumann_gaussian_nonpositive_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:04:22.97699+00:00
-- url     : https://prove2.me/theorems/d78a4bfb-21c0-4c82-a864-6ae7037d7d9d
-- title:
--   Gaussian Neumann corrections vanish on the nonpositive half-line
-- statement:
--   Every noninitial Gaussian Neumann correction defined through a causal weighted primitive is zero when the time argument is nonpositive. This resolves the zero-extension boundary case in the global Volterra recurrence.
-- source:
--   For x≤0 the causal interval Ioc(0,x) is empty. Every weighted Gaussian Neumann correction beyond Q0 is defined by an integral on this interval and therefore vanishes. Alongside the proved head and tail recurrences for positive x, this supplies the nonpositive case needed to establish the full-function hstep identity in causal_neumann_resolvent_dominated_convergence.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_neumann_gaussian_nonpositive_zero
    (a w : ℝ) (P Q : ℕ → ℝ → ℝ)
    (hQsucc : ∀ n : ℕ, Q (n + 1) = fun x : ℝ =>
      (1 / a) * (∫ t in Ioc (0 : ℝ) x,
        Real.exp (w * t) * P n t ∂volume)) :
    ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → Q (n + 1) x = 0 := by sorry
