-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB177_real_symmetric_interval_volume
-- name    : AvramDividend.Classical.avram_gbB177_real_symmetric_interval_volume
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:40:06.782348+00:00
-- url     : https://prove2.me/theorems/e6de562f-bd6a-4f8d-bd5b-1989b2abdfcd
-- title:
--   Lebesgue volume of a symmetric real interval is twice its nonnegative radius
-- statement:
--   The Lebesgue measure of the symmetric real interval about y with radius ε is its nonnegative length, 2ε. Used to turn bounded occupation density into a quantitative small-ball estimate.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB177_real_symmetric_interval_volume (y ε : ℝ) :
    volume (Ioo (y - ε) (y + ε)) =
      ENNReal.ofReal (2 * ε) := by sorry
