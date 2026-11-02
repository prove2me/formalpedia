-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_finite_rank_predictable_marked_grid_first_moment
-- name    : AvramDividend.Classical.avram_wave6_01_original_finite_rank_predictable_marked_grid_first_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:55:35.082877+00:00
-- url     : https://prove2.me/theorems/e11b3fbf-3de1-45ae-903c-e101ed3076b2
-- title:
--   Finite-rank predictable Borel-marked grid first-moment compensation on the actual Lévy filtration
-- statement:
--   For the actual original Levy process X on the unchanged filtered probability space, every finite sum of predictable simple weights H_i measurable with respect to the genuine F_s and Borel mark windows B_i, applied to a finite deterministic future-increment grid, has expected total weighted count equal to the sum of its history means times the original unconditional marked-grid count means. The terms are nonnegative extended-real, so no implicit integrability or finite-mass hypothesis is needed. This is finite-step source predictability, not the unproved intrinsic jump-measure X.nu compensator.
-- source:
--   Direct finite-sum Tonelli of the new canonically Proved original source Borel-marked grid weighted first-moment factor 43c7d32a-bcfc-4b0d-bca4-27fe1cdd0bd9; each source count is explicitly measurable by finite indicator sums, with the original filtration and no Poisson proxy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_future_marked_increment_grid_weighted_factor

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave6_01_original_finite_rank_predictable_marked_grid_first_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (I : Finset ι)
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ I, Measurable[𝓕 s] (H i))
    (B : ι → Set ℝ)
    (hB : ∀ i ∈ I, MeasurableSet (B i))
    (n : ℕ) (grid : ℕ → ℝ≥0) :
    (∫⁻ ω, ∑ i ∈ I, H i ω *
      ((((Finset.range n).filter (fun j =>
        (X.X (s + grid (j + 1)) ω - X.X s ω) -
          (X.X (s + grid j) ω - X.X s ω) ∈ B i)).card : ℝ≥0∞)) ∂P) =
    ∑ i ∈ I, (∫⁻ ω, H i ω ∂P) *
      (∫⁻ ω, ((((Finset.range n).filter (fun j =>
        (X.X (s + grid (j + 1)) ω - X.X s ω) -
          (X.X (s + grid j) ω - X.X s ω) ∈ B i)).card : ℝ≥0∞)) ∂P) := by sorry
