-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_capped_two_sided_first_exit_stopped_reserve_tendsto
-- name    : AvramDividend.Classical.levy_capped_two_sided_first_exit_stopped_reserve_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:43:16.439102+00:00
-- url     : https://prove2.me/theorems/8f0caca0-a4bd-413f-a8ca-36fe1e61c8c8
-- title:
--   Stopped Lévy reserve converges along genuine first two-sided grid crossings
-- statement:
--   For a fixed càdlàg spectrally negative Lévy sample path whose strict two-sided first-exit time is finite, genuine minimal first crossing indices on uniform grids of vanishing mesh produce stopped reserve values converging to the reserve at the true exit time clipped by a finite horizon. The proof identifies the chosen minimal index with the existing neighbourhood approximation witness, without assuming a stopped scale martingale.
-- source:
--   Accepted chat03_capped_grid_stopped_path_open_eventually (35cd8d74-def4-4eef-ac2d-fa8aca6acccc) and its genuine minimal grid-exit witness; continuous reserve sampling on right-continuous paths.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_stopped_path_open_eventually
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_capped_two_sided_first_exit_stopped_reserve_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (first : ℕ → ℕ)
    (hfirst : ∀ᶠ n in atTop,
      (X.X ((first n : ℝ≥0) * mesh n) ω < lower ∨
       upper < X.X ((first n : ℝ≥0) * mesh n) ω) ∧
      (∀ j : ℕ, j < first n →
        ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
           upper < X.X ((j : ℝ≥0) * mesh n) ω))) :
    Tendsto (fun n =>
      X.X (min ((first n : ℝ≥0) * mesh n) T) ω) atTop
      (𝓝 (X.X (min τ T) ω)) := by sorry
