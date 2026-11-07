-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_frozen_prefix_path_filtration_measurable
-- name    : AvramDividend.Classical.avram_bv_jump8_original_frozen_prefix_path_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:57:49.53485+00:00
-- url     : https://prove2.me/theorems/32236cde-ff0d-41a9-bee3-389828ffbd8d
-- title:
--   Original Lévy path frozen at a deterministic horizon is measurably determined by its own filtration history
-- statement:
--   For each T, the whole stopped/frozen original trajectory ω↦(t↦X(min(t,T),ω)) is measurable into the coordinate-product path sigma algebra relative to the source 𝓕_T, since all coordinates occur at times ≤T and the source is adapted.
-- source:
--   Proof from the original X.adapted and the filtration monotonicity, with measurable_pi_iff. Substantive reusable source-adapted child for 154a6ab1; no right-continuous filtration substitution.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_original_frozen_prefix_path_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    Measurable[𝓕 T]
      (fun ω : Ω => fun t : ℝ≥0 => X.X (min t T) ω) := by sorry
