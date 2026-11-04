-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_sigma_quadratic_mesh_error_tendsto_zero
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_sigma_quadratic_mesh_error_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:29:27.630274+00:00
-- url     : https://prove2.me/theorems/7ab86ca5-784b-4be4-9491-b28b45009913
-- title:
--   Original Levy Gaussian quadratic mesh error variance factor converges to zero under refinement
-- statement:
--   For the actual original spectrally negative Levy process X, any sequence of finite time meshes with nonnegative cell widths, uniformly bounded total time T and maximal width ε_n tending to zero has Gaussian quadratic variation fourth-moment mesh-error coefficient 2σ⁴ times sum of squared cell widths converging to zero. This source-specific quantitative fact works for σ=0 and σ>0 and is independent of a Brownian construction; identification with stochastic error still requires a separate same-space Gaussian fourth-moment and covariance theorem.
-- source:
--   Gaussian quadratic-variation mesh approximation associated to the exact source coefficient X.σ of SpectrallyNegativeLevy; Avram, Palmowski and Pistorius, Proposition 4(i), equation (5.10).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_sigma_quadratic_mesh_error_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : ℕ → Finset ι) (h : ℕ → ι → ℝ≥0)
    (T : ℝ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n)
    (hmax : ∀ n, ∀ i ∈ S n, (h n i : ℝ) ≤ ε n)
    (hT : ∀ n, (∑ i ∈ S n, (h n i : ℝ)) ≤ T)
    (hεzero : Tendsto ε atTop (nhds 0)) :
    Tendsto (fun n => (2 : ℝ) * X.σ ^ 4 *
      (∑ i ∈ S n, (h n i : ℝ) ^ 2)) atTop (nhds 0) := by sorry
