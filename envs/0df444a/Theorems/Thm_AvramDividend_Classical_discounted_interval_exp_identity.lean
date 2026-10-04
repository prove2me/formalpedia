-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_interval_exp_identity
-- name    : AvramDividend.Classical.discounted_interval_exp_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T20:51:00.759815+00:00
-- url     : https://prove2.me/theorems/2ccab6d7-d02c-4332-8083-b6adb63344f2
-- title:
--   Evaluate the exponentially discounted interval kernel for the Lévy-tail transform
-- statement:
--   For θ>0 and any real z, the integral from 0 to z of exp(-θt) equals (1-exp(-θz))/θ. In the bounded-variation scale-function proof this evaluates the inner discounted jump-magnitude integral obtained from the layer-cake identity and is used directly in the Lévy-tail transform equation.
-- source:
--   Fundamental theorem of calculus and Real.hasDerivAt_exp at pinned Mathlib 0df444a3; BV Lévy-tail Laplace transform

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Closed form of the exponentially discounted jump-height interval integral. -/
theorem discounted_interval_exp_identity (θ z : ℝ) (hθ : 0 < θ) :
    (∫ t in (0 : ℝ)..z, Real.exp (-θ * t)) =
      (1 - Real.exp (-θ * z)) / θ := by
  sorry

end AvramDividend.Classical
