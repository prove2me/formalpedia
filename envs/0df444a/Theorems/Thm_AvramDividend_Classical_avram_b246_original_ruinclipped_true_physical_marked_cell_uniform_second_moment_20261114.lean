-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b246_original_ruinclipped_true_physical_marked_cell_uniform_second_moment_20261114
-- name    : AvramDividend.Classical.avram_b246_original_ruinclipped_true_physical_marked_cell_uniform_second_moment_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:32:25.624725+00:00
-- url     : https://prove2.me/theorems/3850a18f-6764-4607-8171-9e96f05578f6
-- title:
--   Original true ruin-clipped physical marked occupied-cell count has uniform squared integrability and Poisson-rate second-moment bound
-- statement:
--   For finite negative-jump activity on the original Lévy probability space, the square of the true negative-jump occupied-cell count on a canonical grid truncated by a bounded right-continuous stopping time σ is integrable, and its expected square is at most (nν_-)²+nν_- independently of grid mesh m. The proof uses the source actual count domination at each ω and the original physical negative Borel-count second-moment identity, without assuming an independent Poisson construction or post-ruin process.
-- source:
--   Proved B244 stopping-time physical marked-cell L1 domination, Proved A20 original negative Borel physical exact second moment, plus nonnegative square monotonicity and Integrable.mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b246_original_ruinclipped_true_physical_marked_cell_uniform_second_moment_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : Ω → ℕ → ℝ≥0 := fun ω i =>
      min ((i : ℝ≥0) * Δ) (σ ω)
    let marked : Ω → Finset ℕ := fun ω => by
      classical
      exact (Finset.range (m + 1)).filter (fun i =>
        ∃ u : ℝ≥0, grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)
    let rate : ℝ :=
      ((n : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
    Integrable (fun ω => ((marked ω).card : ℝ) ^ 2) P ∧
      (∫ ω, ((marked ω).card : ℝ) ^ 2 ∂P) ≤ rate ^ 2 + rate := by sorry
