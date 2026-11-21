-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_fullnegative_cutoff_physical_grid_all_pair_crossproducts_integrable
-- name    : AvramDividend.Classical.avram_pj_original_fullnegative_cutoff_physical_grid_all_pair_crossproducts_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:19:04.185342+00:00
-- url     : https://prove2.me/theorems/3e04272f-05d2-4c30-ab99-20cfb40f77b1
-- title:
--   Original complete negative-cutoff predictable compensated grid has all off-diagonal products L1 automatically
-- statement:
--   For the original spectrally negative Lévy full negative finite cutoff count and exact right-continuous physical mesh, all compensated predictable weighted cell increments have finite second moments when their past coefficients are strongly measurable and bounded. Hence every off-diagonal product is integrable under the true original probability P by L2 Cauchy Schwarz. This discharges an important integrability hypothesis of the full-grid signed martingale sum L2 isometry.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_marked_grid_L2_each_cell_implies_all_cross_products_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_fullnegative_cutoff_physical_grid_all_pair_crossproducts_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m cut : ℕ) (Δ : ℝ≥0) (grid : ℕ → ℝ≥0)
    (hStep : ∀ j, grid (j + 1) = grid j + Δ)
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L) :
    let N : ℕ → Ω → ℝ≥0∞ := fun j ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))
        (Ioc (grid j) (grid (j + 1)) ×ˢ
          Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℝ :=
      ((Δ : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let Z : ℕ → Ω → ℝ := fun i ω =>
      H i ω * ((N i ω).toReal - r)
    ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      Integrable (fun ω => Z i ω * Z j ω) P := by sorry
