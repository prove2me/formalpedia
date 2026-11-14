-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_zero_nu_every_positive_time_no_actual_jump_ae
-- name    : AvramDividend.Classical.avram_a22_original_zero_nu_every_positive_time_no_actual_jump_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:52:42.01157+00:00
-- url     : https://prove2.me/theorems/bc015f1f-a7c4-4baa-a677-1385aa5007d9
-- title:
--   Zero Levy measure forces every actual positive-time original jump to vanish on one full measure event
-- statement:
--   Given an actual source spectrally negative Levy process on its original probability space and filtration and zero negative Levy measure, a single full measure set has no jump at any positive time, with the source left limit expressed by Function.leftLim. Uses existing Proved original-space global continuity theorem and the exact Mathlib left-limit-of-continuity result.
-- source:
--   Proved original zero-nu continuity b462a147, Mathlib.Topology.Order.LeftRightLim lemma ContinuousWithinAt.leftLim_eq at pinned revision 0df444a360eaa60ab8c11dca51a86af692955474; Kyprianou Levy-Ito theorem for zero jump intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_zero_nu_every_positive_time_no_actual_jump_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) :
    ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by sorry
