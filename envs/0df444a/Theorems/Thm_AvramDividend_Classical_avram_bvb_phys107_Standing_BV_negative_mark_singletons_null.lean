-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
-- name    : AvramDividend.Classical.avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:18:10.211855+00:00
-- url     : https://prove2.me/theorems/9e152b76-1228-43bf-a2b7-4e1648544877
-- title:
--   Original BV standing assumptions eliminate all point atoms of the Levy measure
-- statement:
--   For every real jump mark, the exact original Standing and bounded-variation assumptions force the Levy measure of that singleton to vanish, ruling out atoms at ruin-contact thresholds.
-- source:
--   Original BV phys95 mark-integrated compensator convergence, using Condition33 atomlessness

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys107_Standing_BV_negative_mark_singletons_null {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing) (hBV : X.BoundedVariation) (z : ℝ) : X.ν ({z} : Set ℝ) = 0 := by sorry
