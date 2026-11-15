-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b249_original_true_ruinclipped_physical_grid_cells_never_after_ruin_20261114
-- name    : AvramDividend.Classical.avram_b249_original_true_ruinclipped_physical_grid_cells_never_after_ruin_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:40:56.518904+00:00
-- url     : https://prove2.me/theorems/9b3831e6-ad78-4e25-adb8-b73b4edb551f
-- title:
--   Every true canonical physical ruin-clipped grid endpoint stays no later than original ruin and deterministic horizon
-- statement:
--   On the original spectrally negative Lévy probability space, each time v_i=min(iΔ,σ(ω)) of the actual canonical physical grid clipped to an admissible finite stopping clock lies no later than ruinTime and the deterministic horizon n. This holds pathwise, including time zero and grid endpoints equal to the ruin time; it preserves the true stopped source and does not use a post-ruin extension.
-- source:
--   Proved avram_p4_d_dividend_original_ruin_truncated_clock_bounded_by_ruin_and_horizon_in_extended_time, true B24 hσclip and monotonicity of min and the ENNReal real embedding.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b249_original_true_ruinclipped_physical_grid_cells_never_after_ruin_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n m : ℕ) (σ : Ω → ℝ≥0)
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ω : Ω) (i : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun j => min ((j : ℝ≥0) * Δ) (σ ω)
    (v i : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      v i ≤ (n : ℝ≥0) := by sorry
