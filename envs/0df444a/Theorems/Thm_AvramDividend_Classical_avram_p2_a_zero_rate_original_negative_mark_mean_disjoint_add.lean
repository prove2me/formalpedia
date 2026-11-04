-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_mark_mean_disjoint_add
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_negative_mark_mean_disjoint_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:02:42.238388+00:00
-- url     : https://prove2.me/theorems/3dd1dd3a-ce7e-46bf-8386-feb3f84d7e67
-- title:
--   Original intrinsic mean jump count is additive on disjoint measurable mark sets
-- statement:
--   For the original spectrally negative Lévy process on the true sample space, establish finite disjoint additivity of the expected marked jump count over two measurable disjoint sets of marks. Derive it from the already Proved original-source mean Borel measure and its measure-theoretic disjoint-union identity, without any Lévy rate or compensation assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_mark_mean_measure

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_negative_mark_mean_disjoint_add
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B C : Set ℝ)
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : Disjoint B C) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (B ∪ C)) ∂P) =
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) + (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ C) ∂P) := by sorry
