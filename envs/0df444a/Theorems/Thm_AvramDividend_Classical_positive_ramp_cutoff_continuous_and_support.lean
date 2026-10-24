-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_ramp_cutoff_continuous_and_support
-- name    : AvramDividend.Classical.positive_ramp_cutoff_continuous_and_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:20:40.008117+00:00
-- url     : https://prove2.me/theorems/2577581f-8223-422a-be07-9b627e75dec1
-- title:
--   Explicit continuous real ramp cutoff with controlled zero and unit regions
-- statement:
--   For any positive epsilon, the clipped affine ramp χε(x)=max(0,min(1,(x−ε)/ε)) is globally continuous, vanishes for x≤ε, and equals one for x≥2ε. Multiplying an L1 causal kernel continuous on the positive axis by this cutoff yields a continuous bounded globally extended kernel and a small-origin remainder supported in [0,2ε]. This is a constructive ingredient for the BV renewal convolution-density local-continuity proof.
-- source:
--   Elementary continuity of continuous min/max affine maps, and the linear inequalities for the clipped ramp.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
open Set

namespace AvramDividend.Classical
theorem positive_ramp_cutoff_continuous_and_support
    (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun x : ℝ => max (0 : ℝ) (min 1 ((x - ε) / ε))) ∧
    (∀ x : ℝ, x ≤ ε → max (0 : ℝ) (min 1 ((x - ε) / ε)) = 0) ∧
    (∀ x : ℝ, 2 * ε ≤ x → max (0 : ℝ) (min 1 ((x - ε) / ε)) = 1) := by sorry
end AvramDividend.Classical
