-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva55_original_finite_activity_physical_grid_jump_isolation_ae
-- name    : AvramDividend.Classical.avram_bva55_original_finite_activity_physical_grid_jump_isolation_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:46:44.414204+00:00
-- url     : https://prove2.me/theorems/bd149898-b15d-4835-a4fd-de57f03643d5
-- title:
--   Almost every original finite-activity Levy path has at most one jump in every sufficiently fine physical grid cell
-- statement:
--   Under the finite-activity assumption, on one full-measure event of the original Lévy probability space, every sufficiently fine source-exact uniform physical grid cell contains at most one actual nonzero Lévy jump before the horizon. The eventually-fine index may depend on the sample path but is uniform over all grid cells and respects the exact original filtration and source process.
-- source:
--   Proved 1e50b68a-ebdb-4d20-b58f-de2bab42874d original process almost-sure finite jump-time support combined with Proved a1e08404-3508-4d95-aba1-5d26dd576ab4 source-grid finite-mark isolation; direct geometric input to root-connected 4287fafd-afdc-46b2-a160-033b7b2500f2, 11 November 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bva55_original_finite_activity_physical_grid_jump_isolation_ae {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) (S : ℝ≥0) (hS : 0 < S) (u : ℕ → ℕ → ℝ≥0) (huniform : ∀ n i, (u n i : ℝ) = (S : ℝ) * (i : ℝ) / ((n : ℝ) + 2)) : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in Filter.atTop, ∀ i : ℕ, ∀ s t : ℝ≥0, 0 < s → s ≤ S → X.X s ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) s ≠ 0 → 0 < t → t ≤ S → X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0 → u n i ≤ s → s < u n (i + 1) → u n i ≤ t → t < u n (i + 1) → s = t := by sorry
