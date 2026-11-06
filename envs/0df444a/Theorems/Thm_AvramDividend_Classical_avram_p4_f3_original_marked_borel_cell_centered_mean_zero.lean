-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_marked_borel_cell_centered_mean_zero
-- name    : AvramDividend.Classical.avram_p4_f3_original_marked_borel_cell_centered_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:55:47.488254+00:00
-- url     : https://prove2.me/theorems/464bd4ab-35fa-408f-a893-4ee6421dfe3e
-- title:
--   Actual original separated marked-cell count minus its Levy compensator has zero mean
-- statement:
--   The actual marked jump count of the original spectrally negative Lévy process on a physical interval (s,t] and separated measurable negative Borel mark B has expected real count (t−s)ν(B). Subtracting this deterministic compensator yields an integrable mean-zero original process cell. The finite original count and real Bochner integrability premises are explicit and separately supported by original source results; no independent point process, Gaussian surrogate or equality-in-law argument is used.
-- source:
--   Proved 5933267b-b40f-483c-a57c-f63294dc12a8 proves the exact physical first-compensator lintegral identity for each past rectangle. Convert its source ENNReal count to a real integral using the explicitly assumed pathwise count finiteness, pinned Mathlib ofReal_integral_eq_lintegral_ofReal and original-space integrability. This directly supplies the first-moment mean-zero part of the original compensated marked-cell martingale required for canonical fdb9a6a3.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_future_negative_borel_rectangle_all_cells
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_marked_borel_cell_centered_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε))
    (A : Ω → ℝ)
    (hAeq : ∀ ω, A ω =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)
    (hNfinite : ∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) < ⊤)
    (hAi : Integrable A P) :
    let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => A ω - r) P ∧
      (∫ ω, A ω - r ∂P) = 0 := by sorry
