-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b243_original_ruinclipped_finiteactivity_true_physical_marked_cell_count_L1_dom
-- name    : AvramDividend.Classical.avram_b243_original_ruinclipped_finiteactivity_true_physical_marked_cell_count_L1_dom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:15:59.873538+00:00
-- url     : https://prove2.me/theorems/15f598f3-fd25-4c2f-93fa-bfec2713ce03
-- title:
--   Original ruin-clipped finite-activity canonical physically marked jump-cell count is measurable integrable and Poisson dominated
-- statement:
--   On the original physically stopped grid v_i=min(i n/(m+1),sigma(omega)), where sigma is a measurable bounded stopping clock, mark exactly those cells containing a genuine nonzero jump of the original spectrally negative Lévy process X. The finite random number of marked physical cells is measurable and integrable, and its count is almost surely dominated by the actual finite negative marked Poisson count on the original horizon (0,n]. This preserves the true ruin-clipped clock and genuine half-open marked cells, supplying the marked-cell L1 domination component required to control the Gaussian/negative-jump Itô error in 61538c12.
-- source:
--   Proved B207 canonical bounded marked grid measurable integrable real Poisson domination specialised to the monotone clipped physical grid. Each clipped endpoint is bounded by sigma≤n and measurable as min of deterministic grid clock and measurable sigma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b207_original_canonical_bounded_marked_grid_measurable_integrable_real_dom
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b243_original_ruinclipped_finiteactivity_true_physical_marked_cell_count_L1_dom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (σ : Ω → ℝ≥0)
    (hσmeas : Measurable σ)
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
