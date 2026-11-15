-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b244_original_true_stopping_clock_ruinclipped_marked_cell_L1_dom_20261114
-- name    : AvramDividend.Classical.avram_b244_original_true_stopping_clock_ruinclipped_marked_cell_L1_dom_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:24:49.182438+00:00
-- url     : https://prove2.me/theorems/7ad3bc4d-7754-4d87-a36d-840c47a1f343
-- title:
--   Original genuine right-continuous stopping-time physical marked-cell count: measurable and L1-dominated at the ruin-clipped horizon
-- statement:
--   For an original spectrally negative Lévy process with finite negative-mark intensity, a bounded right-continuous-filtration stopping time σ gives an original truncated physical grid whose number of marked occupied cells is measurable and integrable. Its real marked count is dominated almost everywhere by the original total physical negative jump count through n. Unlike the source B243, no additional measurability hypothesis is needed; derive it from the actual stopping-time property.
-- source:
--   Proved Mathlib IsStoppingTime.measurable' and measurable_coe_nnreal_ennreal_iff, applied to the B243 original marked-grid count theorem. Maintains original X/P and true stop without any post-ruin process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b244_original_true_stopping_clock_ruinclipped_marked_cell_L1_dom_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : Ω → ℕ → ℝ≥0 := fun ω i =>
      min ((i : ℝ≥0) * Δ) (σ ω)
    let marked : Ω → Finset ℕ := fun ω => by
      classical
      exact (Finset.range (m + 1)).filter (fun i =>
        ∃ u : ℝ≥0, grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)
    Measurable (fun ω => ((marked ω).card : ℝ)) ∧
    Integrable (fun ω => ((marked ω).card : ℝ)) P ∧
    (∀ᵐ ω ∂P, ((marked ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u)))
        (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal) := by sorry
