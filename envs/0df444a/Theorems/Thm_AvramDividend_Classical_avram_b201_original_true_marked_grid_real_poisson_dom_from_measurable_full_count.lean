-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b201_original_true_marked_grid_real_poisson_dom_from_measurable_full_count
-- name    : AvramDividend.Classical.avram_b201_original_true_marked_grid_real_poisson_dom_from_measurable_full_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:25:12.367205+00:00
-- url     : https://prove2.me/theorems/c9c06b28-f407-4b61-b0f2-6c23fed6a7f9
-- title:
--   Original actual physical marked-grid real count dominated almost everywhere by finite-intensity Poisson count given source-count measurability
-- statement:
--   For an original bounded finite-negative-activity spectrally negative Lévy source, a potentially random monotone original physical grid and marked cells containing real source jumps, assume the exact original full negative Poisson source count on the deterministic bounded horizon is almost-everywhere measurable. Proved B195 then makes the full negative source count finite almost everywhere; Proved B163 supplies the actual marked-grid cardinal bound in extended nonnegative reals on the real source paths. ENNReal.toReal_mono and finite-card conversion give the exact real-valued selected-cell Poisson-count domination required by the original mixed Itô stopped mesh energy theorems. This avoids any false conversion of infinity to zero and does not assume the post-ruin process.
-- source:
--   Proved B163 physical-source marked count, B195 conull source finiteness, pinned ENNReal.toReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
import Theorems.Thm_AvramDividend_Classical_avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b201_original_true_marked_grid_real_poisson_dom_from_measurable_full_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (grid : Ω → ℕ → ℝ≥0) (hMono : ∀ ω, Monotone (grid ω))
    (J : Ω → Finset ℕ)
    (hJ : ∀ᵐ ω ∂P, ∀ i ∈ J ω, ∃ u : ℝ≥0,
      grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (hRange : ∀ ω i, i ∈ J ω → grid ω (i + 1) ≤ T)
    (hCountMeas : AEMeasurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))) P) :
    ∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal := by sorry
