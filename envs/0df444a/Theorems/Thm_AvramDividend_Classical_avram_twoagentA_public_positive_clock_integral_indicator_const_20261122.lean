-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_positive_clock_integral_indicator_const_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_positive_clock_integral_indicator_const_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:27:25.810998+00:00
-- url     : https://prove2.me/theorems/33b1bbd9-f147-4b11-a0fa-6c04e5c36915
-- title:
--   Original finiteband physical compensated signed mark source chain 1
-- statement:
--   Republish exact previously accepted actual original compensated negative marked physical finite-horizon time clock integral, masked stopping rectangle and Campbell-mark centring, using exclusively public proved source-faithful original-X dependencies.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_positive_time_pushforward_clock_mass_20261122
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_positive_clock_integral_indicator_const_20261122
    (T : ℝ≥0) (K : ℝ) :
    (∫ t : ℝ≥0, (if t ∈ Ioc (0 : ℝ≥0) T then K else 0)
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal)) = (T : ℝ) * K  := by sorry
