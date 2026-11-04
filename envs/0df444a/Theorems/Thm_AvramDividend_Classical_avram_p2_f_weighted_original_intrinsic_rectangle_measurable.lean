-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_rectangle_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:26:38.207045+00:00
-- url     : https://prove2.me/theorems/d9c55240-a92c-47c2-925f-336ed7cf5d08
-- title:
--   Exact original marked-future rectangle count is measurable in the source sample space
-- statement:
--   For the actual spectrally negative Lévy process and any measurable Borel mark cell B, the literal original jump-count N_X((s,s+T]×B) is measurable as an ENNReal-valued random variable on unchanged Ω, without requiring an intensity, finite activity, negative marks or rate identification. Source-faithful measurable count is useful to the original predictable compensator P2-E and to nonnegative weighted lintegral reasoning.
-- source:
--   Exact Proved original marked count measurable shifted-future extractor 5cf3e058 and shifted original future coordinate-product measurability 8b9eb23c; no ν-rate, original source X P 𝓕 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_rectangle_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun ω : Ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)) := by sorry
