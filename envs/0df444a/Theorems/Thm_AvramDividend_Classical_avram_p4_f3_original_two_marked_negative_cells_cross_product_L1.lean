-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_two_marked_negative_cells_cross_product_L1
-- name    : AvramDividend.Classical.avram_p4_f3_original_two_marked_negative_cells_cross_product_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:06:16.528713+00:00
-- url     : https://prove2.me/theorems/c2cf36e5-c71b-45f6-bafd-cb6b29ad79ab
-- title:
--   Original disjoint or overlapping marked negative-jump cells have integrable cross products
-- statement:
--   For any two actual marked jump-count cells of one original spectrally negative Lévy process, with both finite physical time windows inside T and measurable mark sets separated below −1/(n+1), the real-valued product of their original physical counts is Bochner integrable. The cells may have overlapping or disjoint time and mark windows. This follows from source-specific individual second-moment budgets and a quadratic domination of the product by the sum of squares. It discharges the off-diagonal product-integrability prerequisite for finite-grid isometry, without assuming independent copies or cross-moment factorisation.
-- source:
--   Proved original marked negative subband explicit quadratic budget 367c2c5e-28cf-48b6-aadc-aaa41f79b3c5 and actual marked-cell measurability from P2 theorem avram_p2_d_future_intrinsic_general_time_mark_measurable. Both original physical cell counts are square-integrable, hence their product is integrable by |ab| ≤ a²+b². Future covariance requires a separate actual source moment identity.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_marked_negative_subband_explicit_quadratic_budget
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_two_marked_negative_cells_cross_product_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (s₁ t₁ s₂ t₂ : ℝ≥0)
    (hst₁ : s₁ ≤ t₁) (htT₁ : t₁ ≤ T)
    (hst₂ : s₂ ≤ t₂) (htT₂ : t₂ ≤ T)
    (B₁ B₂ : Set ℝ)
    (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂)
    (hSep₁ : B₁ ⊆ Iic (-(1 / ((n : ℝ) + 1))))
    (hSep₂ : B₂ ⊆ Iic (-(1 / ((n : ℝ) + 1)))) :
    let N₁ : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s₁ t₁ ×ˢ B₁)
    let N₂ : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s₂ t₂ ×ˢ B₂)
    Integrable (fun ω => (N₁ ω).toReal * (N₂ ω).toReal) P := by sorry
