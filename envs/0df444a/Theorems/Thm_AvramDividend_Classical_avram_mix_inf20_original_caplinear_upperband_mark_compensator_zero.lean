-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_caplinear_upperband_mark_compensator_zero
-- name    : AvramDividend.Classical.avram_mix_inf20_original_caplinear_upperband_mark_compensator_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:23:25.501109+00:00
-- url     : https://prove2.me/theorems/c82da644-9594-4436-b222-839894146689
-- title:
--   Original infinite-jump caplinear upper-band compensated mark integrand vanishes exactly
-- statement:
--   Original infinite-activity caplinear upper-strip compensated Levy mark cancellation. With V the corrected affine extension of candidate w above finite barrier b, whenever both the reserve y before a marked jump z and the postmark reserve y+z lie strictly above b, the generator integrand V(y+z)-V(y)-V'(y)z vanishes identically. Uses the server-Proved affine derivative theorem avram_gbB31_interior_caplinear_affine_upper_derivatives; this is the exact deterministic marked-jump algebra required to eliminate erroneous raw-w above-cap contributions in the finite-cap compensated Ito source. No stochastic compensation, boundedness or positive-survival assertion is silently assumed.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB31_interior_caplinear_affine_upper_derivatives
open Filter Set AvramDividend.Classical
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_caplinear_upperband_mark_compensator_zero
    (w : ℝ → ℝ) (b y z : ℝ)
    (hy : b < y) (hyz : b < y + z) :
    let V : ℝ → ℝ := fun t => if t ≤ b then w t else w b + (t - b)
    V (y + z) - V y - deriv V y * z = 0 := by sorry
