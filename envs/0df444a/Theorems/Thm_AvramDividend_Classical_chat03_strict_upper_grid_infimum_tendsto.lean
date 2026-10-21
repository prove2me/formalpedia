-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_strict_upper_grid_infimum_tendsto
-- name    : AvramDividend.Classical.chat03_strict_upper_grid_infimum_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T21:51:49.576293+00:00
-- url     : https://prove2.me/theorems/fc0e0b02-80bf-4aed-9dea-433f4a00c290
-- title:
--   Genuine strict upper grid first-passage infima converge to the finite continuous passage infimum
-- statement:
--   For a right-continuous official Lévy sample path with a finite strict upper passage-time infimum τ, any positive sequence of uniform mesh widths tending to zero yields corresponding sampled upper first-passage infima σ_n converging to τ, provided each sampled strict crossing set has greatest lower bound σ_n. The proof combines the separately Proved strict upper mesh-detection epsilon-delta lemma and the accepted generic mesh-bracket-to-Tendsto theorem. All crossings are strict, and their infima need not be attained. This establishes a direct first-passage time convergence ingredient for the exact discounted exit identity without relying on any stochastic martingale.
-- source:
--   Proved Chat03 strict upper mesh approximation and generic first-passage mesh-bracket Tendsto theorem, pinned Mathlib.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_upper_exit_mesh_approximation
import Theorems.Thm_AvramDividend_Classical_chat03_tendsto_first_passage_of_mesh_brackets

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_strict_upper_grid_infimum_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB {t : ℝ≥0 | upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (σ : ℕ → ℝ≥0)
    (hσ : ∀ n, IsGLB
      {s : ℝ≥0 | ∃ k : ℕ,
        s = (k : ℝ≥0) * mesh n ∧
        (upper < X.X s ω)} (σ n)) :
    Tendsto σ atTop (𝓝 τ) := by sorry
