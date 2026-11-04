-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_mesh_ceiling_sequence_tendsto
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_ruin_mesh_ceiling_sequence_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:43:11.064507+00:00
-- url     : https://prove2.me/theorems/84988e7d-8b9c-449c-8652-2c803c68dd20
-- title:
--   Exact ruin-clipped source clock is pathwise limit of finite deterministic first-ceiling meshes
-- statement:
--   For the unchanged original stopped ruin time and any sequence of monotone finite horizon-covering grids whose mesh δk tends to zero, there exist genuine first-ceiling grid indices with sampled times converging to the exact original stopped time for every path. This is from-above convergence and has no implied martingale L1 bound or Stieltjes from-below cofinal cash property.
-- source:
--   Proved P4-E original first-ceiling mesh and clock squeeze, source exact truncated ruin bounds.

import Mathlib
import Mathlib.Data.Nat.Find
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_first_ceiling_clock_mesh_error
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_grid_clock_squeeze_tendsto

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact source ruin-clipped clock has finite first-ceiling grids converging from above. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_ruin_mesh_ceiling_sequence_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (e : ℕ → ℕ → ℝ≥0) (he : ∀ k, Monotone (e k))
    (N : ℕ → ℕ) (hN : ∀ k, (n : ℝ≥0) ≤ e k (N k))
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (h0 : ∀ k, e k 0 = 0)
    (hStep : ∀ k i, e k (i + 1) ≤ e k i + δ k) :
    ∃ K : ℕ → Ω → ℕ,
      ∀ ω, Tendsto (fun k => e k (K k ω)) atTop (𝓝 (τ ω)) := by sorry
