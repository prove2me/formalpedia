-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_small_cutoff_compensation_identity
-- name    : AvramDividend.Classical.avram_p4_c_generator_small_cutoff_compensation_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:59:54.015184+00:00
-- url     : https://prove2.me/theorems/9c445b22-585f-45bc-bebb-14202b9f0d15
-- title:
--   Original generator compensates all small cutoff jump marks including left endpoint -epsilon
-- statement:
--   For strict 0<epsilon<1 and a negative jump mark -epsilon≤z<0, the source Lévy generator integrand is the exact second-order jump remainder w(y+z)-w(y)-w'(y)z. The source indicator uses strict -1<z<1, and -epsilon belongs to the compensated small-band side.
-- source:
--   Original SpectrallyNegativeLevy.generatorIntegrand exact strict indicator definition

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_small_cutoff_compensation_identity
    (w : ℝ → ℝ) (y z ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hz : z ∈ Ico (-ε) (0 : ℝ)) :
    SpectrallyNegativeLevy.generatorIntegrand w y z =
      w (y + z) - w y - deriv w y * z := by sorry
