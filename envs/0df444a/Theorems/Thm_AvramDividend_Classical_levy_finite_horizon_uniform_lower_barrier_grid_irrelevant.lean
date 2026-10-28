-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finite_horizon_uniform_lower_barrier_grid_irrelevant
-- name    : AvramDividend.Classical.levy_finite_horizon_uniform_lower_barrier_grid_irrelevant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:16:36.198217+00:00
-- url     : https://prove2.me/theorems/05622aaf-6210-4c99-8b54-d7f911e1f534
-- title:
--   A single finite-horizon lower barrier leaves all capped upper-grid hitting indices unchanged
-- statement:
--   For every càdlàg spectrally negative Lévy sample path and finite time horizon T, there is one real lower barrier b below the entire path on [0,T]. On every deterministic observation grid, with every preterminal observation before T, the first capped hitting index for an upper threshold or crossing below b is exactly the capped first upper-crossing index. Crucially, b is uniform over all grids and caps, enabling the accepted two-sided finite-grid pathwise convergence theorem to be transferred to upper-only first passage.
-- source:
--   Accepted Lévy finite-horizon path lower-boundedness 3bff0b3d-b21d-4639-8902-1ce473fce724 and accepted before-terminal bounded hitting-index congruence e8ec750e-933a-4eac-af32-4dcd134b2024. Finite-horizon lower-barrier exhaustion step in the independent one-sided exponential optional-stopping route.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_congr_before_terminal
import Mathlib.Probability.Process.HittingTime

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_finite_horizon_uniform_lower_barrier_grid_irrelevant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (z : ℝ) :
    ∃ b : ℝ, ∀ (clock : ℕ → ℝ≥0) (m : ℕ),
      (∀ j : ℕ, j < m → clock j ≤ T) →
      hittingBtwn
        (fun k η => max (X.X (clock k) η - z) (b - X.X (clock k) η))
        (Ioi (0 : ℝ)) 0 m ω =
      hittingBtwn
        (fun k η => X.X (clock k) η - z)
        (Ioi (0 : ℝ)) 0 m ω := by sorry
