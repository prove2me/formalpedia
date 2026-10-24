-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_ramp_mul_of_continuousOn_positive
-- name    : AvramDividend.Classical.continuous_ramp_mul_of_continuousOn_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:27:08.463263+00:00
-- url     : https://prove2.me/theorems/0f3e6c45-2d10-45fc-9aaa-99060b7540d3
-- title:
--   A positive-time continuous kernel becomes globally continuous after multiplication by a ramp cutoff
-- statement:
--   Let f be continuous on (0,∞) and ε>0. Multiplying f by the continuous clipped ramp χε, which vanishes for x≤ε, gives a globally continuous function. At x>0 this is the product of continuous functions; at x≤0 it is identically zero throughout the neighbourhood x<ε. This is the key extension lemma for the small-origin decomposition in BV renewal convolution continuity.
-- source:
--   Compose positive-domain continuity with explicit proved ramp. At nonpositive points, use eventually equality to zero on Iio epsilon.

import Mathlib.Topology.ContinuousOn
import Theorems.Thm_AvramDividend_Classical_positive_ramp_cutoff_continuous_and_support
open AvramDividend.Classical Set Filter

namespace AvramDividend.Classical
theorem continuous_ramp_mul_of_continuousOn_positive
    (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Ioi (0 : ℝ))) :
    Continuous (fun x : ℝ => max (0 : ℝ) (min 1 ((x - ε) / ε)) * f x) := by sorry
end AvramDividend.Classical
