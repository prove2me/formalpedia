-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightCont_integer_grid_orthogonal
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_integer_grid_orthogonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:44:27.208681+00:00
-- url     : https://prove2.me/theorems/72d88767-d3c0-4c3d-ad9d-2a8b65d60c54
-- title:
--   Original right-continuous Lévy-filtration grid: orthogonal L² compensated increments
-- statement:
--   For the original spectrally negative Lévy process on its actual sample space, square-integrable differences adapted to integer-time samples of the source right-continuous filtration and conditionally centred one time step earlier are pairwise orthogonal. This is the finite-grid cross-term computation needed for the original small-jump L² isometry. Conditional centring is an explicit genuine stochastic hypothesis.
-- source:
--   Source-based conditional-expectation proof adapted from accepted MDSAux.integral_mul_mds_eq_zero (Prove2Me 6d7721ef-260a-43c3-9cee-8806e3a3f084) and Mathlib.Probability.Process.Filtration.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_integer_grid_orthogonal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (V : ℕ → Ω → ℝ)
    (hmem : ∀ j : ℕ, MemLp (V j) 2 P)
    (hadapt : ∀ j : ℕ, StronglyMeasurable[𝓕.rightCont ((j + 1 : ℕ) : ℝ≥0)] (V j))
    (hmds : ∀ j : ℕ, P[V j | 𝓕.rightCont (j : ℝ≥0)] =ᵐ[P] 0)
    {i j : ℕ} (hij : i < j) :
    ∫ ω, V i ω * V j ω ∂P = 0 := by sorry
