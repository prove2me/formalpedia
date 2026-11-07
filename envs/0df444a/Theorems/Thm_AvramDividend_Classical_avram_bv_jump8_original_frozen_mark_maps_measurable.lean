-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_frozen_mark_maps_measurable
-- name    : AvramDividend.Classical.avram_bv_jump8_original_frozen_mark_maps_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:11:13.267404+00:00
-- url     : https://prove2.me/theorems/918d0cba-2f0b-4978-a2b2-33cff8b9e9ad
-- title:
--   Both original and frozen genuine Lévy time-mark functions are Borel measurable for every source sample
-- statement:
--   The original source path and its frozen-at-n variant are both càdlàg for every sample, so their time-to-jump-mark maps are Borel. This supplies the exact measurability hypotheses for the generic marked-count equality. It is independent of finite-activity or Poisson process assumptions.
-- source:
--   Use original source X.rightCont and X.leftLim, Proved frozen source càdlàg c7626437, and pinned Borel theorem for càdlàg paths / measurable left-limit functions, then hPath.sub hLeft with measurable_id.prodMk as in Proved ab9dba1f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_original_frozen_mark_maps_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n : ℕ) :
    Measurable (fun u : ℝ≥0 => (u, X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) ∧
    Measurable (fun u : ℝ≥0 => (u, X.X (min u (n : ℝ≥0)) ω -
      Function.leftLim (fun v : ℝ≥0 => X.X (min v (n : ℝ≥0)) ω) u)) := by sorry
