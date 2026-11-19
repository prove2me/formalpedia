-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_refining_physical_grid_cover
-- name    : AvramDividend.Classical.avram_jump6_B_original_refining_physical_grid_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T16:19:45.346094+00:00
-- url     : https://prove2.me/theorems/f84a436f-bb50-43b0-bfeb-4b3ce825aeda
-- title:
--   Original subordinate stopped clocks admit a deterministic refining physical grid covering the actual horizon
-- statement:
--   For an original spectrally negative Levy process, the true subordinate stopped clock sigma(k) lies below the original ruin-truncated integer horizon N by the Proved source clock theorem. The canonical refining physical grid u(j,i)=i/(j+1), with m(j)=(N+1)(j+1), has zero origin, is monotone in its cell index, and covers sigma(k) for every cell stage. This supplies the exact grid prerequisites for an original Ito-Meyer source certificate without finite activity or a surrogate stopped process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_physical_sigma_clock_le_finite_horizon
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_refining_physical_grid_cover
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (N : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (N : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    let u : ℕ → ℕ → ℝ≥0 := fun j i =>
      (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
    let m : ℕ → ℕ := fun j => (N + 1) * (j + 1)
    (∀ j, Monotone (u j)) ∧
    (∀ j, u j 0 = 0) ∧
    (∀ k ω, ∀ᶠ j in atTop, σ k ω ≤ u j (m j)) := by sorry
