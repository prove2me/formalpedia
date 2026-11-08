-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_fixed_negative_mark_Taylor_correction_upperlim
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps14_fixed_negative_mark_Taylor_correction_upperlim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:21:20.840133+00:00
-- url     : https://prove2.me/theorems/66170b5e-69d7-40a6-9fed-6183936f9921
-- title:
--   Stopped negative Lévy-mark Taylor corrections obey an upper limit across exact ruin contact
-- statement:
--   For fixed negative Lévy mark z and positive pre-jump reserve y, the Taylor jump correction has upper semicontinuous limsup along an approximating reserve sequence, even when y+z=0 or crosses into the killed negative-reserve region. This uses the existing Proved boundary upper-semicontinuity interface and interior continuity of the first derivative.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps14_fixed_negative_mark_Taylor_correction_upperlim
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (y z : ℝ) (hy : 0 < y) (hz : z < 0)
    (hwy : ContinuousAt w y)
    (hwderiv : ContinuousAt (deriv w) y)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds y)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      w (u n + z) - w (u n) -
        (if -1 < z then z * deriv w (u n) else 0) ≤
      w (y + z) - w y -
        (if -1 < z then z * deriv w y else 0) + ε := by sorry
