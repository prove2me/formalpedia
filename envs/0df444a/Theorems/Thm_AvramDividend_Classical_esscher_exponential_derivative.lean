-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_exponential_derivative
-- name    : AvramDividend.Classical.esscher_exponential_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:45:17.71134+00:00
-- url     : https://prove2.me/theorems/551a3497-4ca0-4c34-9ba9-f16698f782aa
-- title:
--   Exact real derivative of an Esscher exponential weight
-- statement:
--   For any real Esscher exponent phi, the derivative in x of exp(-phi*x) is exp(-phi*x)*(-phi). This standard chain-rule identity is isolated to avoid repeated elaboration/typeclass mismatches in the more complex tilted-scale-function monotonicity proof.
-- source:
--   Pinned Mathlib Real.hasDerivAt_exp, HasDerivAt.const_mul and HasDerivAt.comp.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_exponential_derivative (φ x : ℝ) :
    deriv (fun y : ℝ => Real.exp (-φ * y)) x =
      Real.exp (-φ * x) * (-φ) := by sorry
