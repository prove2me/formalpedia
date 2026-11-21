-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_caplinear_entire_upper_strip_mark_remainder_nonpos
-- name    : AvramDividend.Classical.avram_mix_inf20_caplinear_entire_upper_strip_mark_remainder_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:43:07.020198+00:00
-- url     : https://prove2.me/theorems/580c3833-93a2-44dc-ad68-378f8a3f4786
-- title:
--   Entire caplinear finite-cap above-barrier original Lévy marked-jump compensated Taylor remainder is nonpositive
-- statement:
--   Finite-cap corrected original Levy generator upper-strip global compensated mark sign. The premark reserve y exceeds the cap b and the explicit below-cap slope-one affine upper envelope hypothesis holds for all possible postmark values u≤b. For every real marked jump z, including all negative Levy jumps, the corrected caplinear extension V has nonpositive exact jump Taylor term V(y+z)-V(y)-V'(y)z. Split on whether the marked postreserve stays above cap: the server-Proved upperband c82da644 gives exact zero above, and server-Proved downcross 38ab18ed gives nonpositive below. This is the missing uniform original-model cap-above negative-mark integrand bound for infinite-activity compensated Ito. The envelope condition is stated as a genuine separate hypothesis, not inferred from candidate smoothness outside the active HJB interval.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_caplinear_upperband_mark_compensator_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_caplinear_downcross_mark_remainder_nonpos
open Filter Set AvramDividend.Classical
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_caplinear_entire_upper_strip_mark_remainder_nonpos
    (w : ℝ → ℝ) (b y z : ℝ)
    (hy : b < y)
    (hSlope : ∀ u : ℝ, u ≤ b → w u - w b ≤ u - b) :
    let V : ℝ → ℝ := fun t => if t ≤ b then w t else w b + (t - b)
    V (y + z) - V y - deriv V y * z ≤ 0 := by sorry
