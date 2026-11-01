-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_dyadic_residual_values_one_finite_set
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_dyadic_residual_values_one_finite_set
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:23:24.246507+00:00
-- url     : https://prove2.me/theorems/a00d1be4-76b5-4ea9-b984-e0f191fc693c
-- title:
--   The actual finite-activity BV Lévy residual visits one fixed finite set across every dyadic refinement
-- statement:
--   For the genuine original source Lévy process under BV and finite negative Lévy intensity, on one probability-one event the drift-residual observations at all levels and all indices of any aligned uniform dyadic grid belong to a single finite set S(ω). This strengthens the existing per-level cardinal bound into a fixed finite range. It is the missing analytic predecessor to a finite-step original-path representation and eventual genuine-jump count identification, not an assumption of Poisson jump laws.
-- source:
--   Canonical Proved b93e9d7e-e1a9-42f5-968a-560566e554ab bounds the per-level cardinality on a common full event. Nested dyadic grids give monotone finite sets of observed original-path values, and Nat.sSup_mem plus Finset.eq_of_subset_of_card_le establishes finite stabilisation. No independent sample space is introduced. Parent original-filtration source-compensator target 393b03a8-2e9a-43d8-b415-854d86d58104 remains Open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_aligned_dyadic_values_card_uniform_ws01b

open MeasureTheory Set Finset AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_dyadic_residual_values_one_finite_set
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (grid : ℕ → ℕ → ℝ≥0) (T : ℝ)
    (hAlign : ∀ n i : ℕ, grid (n + 1) (2 * i) = grid n i)
    (hGridMono : ∀ n, Monotone (grid n))
    (hMesh : ∀ n i : ℕ, i < 2 ^ n →
      (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ) =
        T / ((2 ^ n : ℕ) : ℝ))) :
    ∀ᵐ ω ∂P, ∃ S : Finset ℝ, ∀ (n i : ℕ), i ≤ 2 ^ n →
      (grid n i : ℝ) * X.drift - X.X (grid n i) ω ∈ S := by sorry
