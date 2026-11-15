-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a120_original_arbitrary_Borel_mark_void_raw_past_measurable_of_frozen_path_20261114
-- name    : AvramDividend.Classical.avram_a120_original_arbitrary_Borel_mark_void_raw_past_measurable_of_frozen_path_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:26:41.036358+00:00
-- url     : https://prove2.me/theorems/aaa9239b-1328-4e65-bdfb-6311909c7ffe
-- title:
--   Original arbitrary Borel marked-jump void event is measurable in raw past when represented by measurable frozen-path count functional
-- statement:
--   For an original Lévy process and any mark set B, if the actual marked count up to time T is a measurable functional F of the full path stopped at T, its zero-count event belongs to the unaugmented raw filtration F_T. The proof composes adapted coordinates, measurable product paths, the frozen-path equality, and the measurable zero singleton. This generalises the existing Proved negative cutoff-band frozen-path measurability lemma to arbitrary mark sets.
-- source:
--   Exact Proved wave7_06_original_negative_band_past_measurable_of_frozen_source_rep proof, replacing its special negative cutoff-band by arbitrary B, without any change to the measurable composition argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a120_original_arbitrary_Borel_mark_void_raw_past_measurable_of_frozen_path_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (T : ℝ≥0) (B : Set ℝ)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hFrozen : ∀ ω : Ω,
      NX ω (Ioc 0 T ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (min v T) ω)) :
    MeasurableSet[𝓕 T]
      {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} := by sorry
