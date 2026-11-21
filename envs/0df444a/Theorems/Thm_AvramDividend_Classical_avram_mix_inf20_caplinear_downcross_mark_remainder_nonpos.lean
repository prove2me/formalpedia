-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_caplinear_downcross_mark_remainder_nonpos
-- name    : AvramDividend.Classical.avram_mix_inf20_caplinear_downcross_mark_remainder_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:35:16.43259+00:00
-- url     : https://prove2.me/theorems/38ab18ed-69e9-45d2-b5b8-a560f5406371
-- title:
--   Caplinear original Levy negative-mark cap-downcross compensated Taylor correction nonpositive
-- statement:
--   Exact original corrected finite-cap marked Levy downcrossing correction for caplinear V: whenever the premark reserve is strictly above the cap b and a negative marked jump crosses to at/below b, and the candidate is bounded above by the affine cap slope-one extension at the postjump state, the compensated Taylor term V(y+z)-V(y)-V'(y)z is nonpositive. The premark derivative is exactly one by Proved avram_gbB31_interior_caplinear_affine_upper_derivatives. The cross-cap slope condition is stated explicitly, so the lemma remains sound without assuming an unproved global derivative bound at the cap. It complements the proved all-upper-band zero mark term c82da644, and is a deterministic building block for original spectrally negative Levy infinite-jump finitecap Ito generator compensation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB31_interior_caplinear_affine_upper_derivatives
open Filter Set AvramDividend.Classical
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_caplinear_downcross_mark_remainder_nonpos
    (w : ℝ → ℝ) (b y z : ℝ)
    (hy : b < y) (hz : y + z ≤ b)
    (hSlope : w (y + z) - w b ≤ y + z - b) :
    let V : ℝ → ℝ := fun t => if t ≤ b then w t else w b + (t - b)
    V (y + z) - V y - deriv V y * z ≤ 0 := by sorry
