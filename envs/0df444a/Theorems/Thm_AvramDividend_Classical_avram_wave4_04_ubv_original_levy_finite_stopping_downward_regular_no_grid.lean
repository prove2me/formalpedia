-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_original_levy_finite_stopping_downward_regular_no_grid
-- name    : AvramDividend.Classical.avram_wave4_04_ubv_original_levy_finite_stopping_downward_regular_no_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:27:15.395225+00:00
-- url     : https://prove2.me/theorems/66982d13-ea38-4a01-9f6c-49753efab1c0
-- title:
--   Original unbounded-variation Lévy path is immediately downward regular after every finite filtration stopping time, with no grid assumptions
-- statement:
--   Let X be the original spectrally negative Lévy process with unbounded variation on its given filtration and τ a genuine finite stopping time of that same filtration. Almost surely, every positive post-stopping time window contains an original path increment strictly below X(τ). No externally provided dense grid or horizon sequence is required. The proof constructs dense observation schedules and reciprocal cofinal horizons in NNReal, transfers original downward regularity to the grid, then applies the independently Proved source finite-stopping strong-Markov downcrossing theorem. This is a source-path stochastic regularity fact, not a marginal-law coupling, compensated jump formula, or dividend HJB bound.
-- source:
--   Strong Markov on original process 877dfbc1-79af-4667-be5c-d0fabce594c0, original UBV downward regularity 703dc740-a8df-4cd1-9ff1-622fd81d68c7, dense-grid equivalence 561313a4-b044-4484-90c2-8cd1ceb9244e. Derived as a publicly reusable source-only subtheorem from the independently accepted same-X,D finite-stopping reserve theorem aa42a21a-9b17-47b3-b72d-a6efd383ae5c; explicit source proof freshly submitted for private compiler verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_ubv_original_levy_finite_stopping_downward_regular_no_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        X.X (τ ω + s) ω - X.X (τ ω) ω < 0 := by sorry
