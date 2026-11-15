-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_ruinclipped_finiteactivity_weighted_marked_grid_L1_integrable
-- name    : AvramDividend.Classical.avram_b24_original_ruinclipped_finiteactivity_weighted_marked_grid_L1_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:34:40.232203+00:00
-- url     : https://prove2.me/theorems/981ce956-867c-4295-9101-2430b7215e18
-- title:
--   Original true ruin-clipped physical weighted marked-cell remainder integrable from canonical marked-count source
-- statement:
--   For the original finite-activity spectrally negative Levy X and actual stopped physical grid, if each genuine marked-cell weight is uniformly bounded and the weighted sum is measurable, then the source weighted marked jump sum is integrable by the Proved genuine jump count L1 bound. Uses original jumps, actual σ and no artificial independent jump martingale.
-- source:
--   Proved B243 canonical true stopped physical marked count and generic bounded marked sum integrability theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_ruinclipped_finiteactivity_weighted_marked_grid_L1_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (σ : Ω → ℝ≥0)
    (hσmeas : Measurable σ)
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (W : ℕ → Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hW : ∀ i ω, |W i ω| ≤ L) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : Ω → ℕ → ℝ≥0 := fun ω i =>
      min ((i : ℝ≥0) * Δ) (σ ω)
    let marked : Ω → Finset ℕ := fun ω => by
      classical
      exact (Finset.range (m + 1)).filter (fun i =>
        ∃ u : ℝ≥0, grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)
    AEStronglyMeasurable (fun ω => ∑ i ∈ marked ω, W i ω) P →
    Integrable (fun ω => ∑ i ∈ marked ω, W i ω) P:= by sorry
