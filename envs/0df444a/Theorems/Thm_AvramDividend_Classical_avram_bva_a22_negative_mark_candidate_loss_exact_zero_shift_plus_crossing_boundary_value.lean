-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_negative_mark_candidate_loss_exact_zero_shift_plus_crossing_boundary_value
-- name    : AvramDividend.Classical.avram_bva_a22_negative_mark_candidate_loss_exact_zero_shift_plus_crossing_boundary_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:52:00.659741+00:00
-- url     : https://prove2.me/theorems/05c008ff-5cc0-47c6-a0b3-0c0b8a768726
-- title:
--   Original spectrally negative mark candidate loss decomposes exactly into zero-at-zero shifted candidate loss and w(0) times ruin-crossing indicator
-- statement:
--   For the original dividend verification candidate w that is zero below the ruin boundary, a positive pre-jump reserve y and a strictly negative jump mark z, decompose the exact candidate decrement w(y)-w(y+z) into the decrement of its zero-shifted interior extension w(y)-w(0) with shifted continuation only when y+z>=0, plus the exact boundary-value crossing contribution w(0)*1_{y+z<0}. The algebra is valid even when w(0)>0. Integrating the second term over y∈(0,epsilon] produces w(0)*min(epsilon,−z), precisely the already Proved original BV truncated negative Lévy first-moment boundary layer. This is a source-faithful method for removing the unnecessary w(0)=0 assumption from the old Bv drift10 spatial jump budget, without finite activity, surrogate source or global generator L1. The measure-level Fubini argument remains a separate mathematical obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_negative_mark_candidate_loss_exact_zero_shift_plus_crossing_boundary_value
    (w : ℝ → ℝ) (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (y z : ℝ) (hy : 0 < y) (hz : z < 0) :
    w y - w (y + z) =
      ((w y - w 0) -
        (if y + z < 0 then 0 else w (y + z) - w 0)) +
      (if y + z < 0 then w 0 else 0) := by sorry
