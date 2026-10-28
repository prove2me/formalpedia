-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_exp_expectation_of_ae_convergence
-- name    : AvramDividend.Classical.levy_capped_upper_grid_exp_expectation_of_ae_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:26:45.701836+00:00
-- url     : https://prove2.me/theorems/2a2fd34b-907d-445d-93dc-9c76d71729a0
-- title:
--   Transfer almost-sure convergence of capped upper-grid Lévy exponentials to convergence of their expectations
-- statement:
--   Let a family of monotone grids have uniformly bounded terminal horizon N. For each grid stop the compensated positive-Laplace Lévy exponential at the first sampled upper upcrossing capped by its final index. If these nonnegative random variables converge almost surely to an a.e. strongly measurable limit Z, then Z is integrable and their expectations converge to E[Z]. Uniform second-moment bounds and square integrability, established independently without an unstopped scale martingale, guarantee uniform integrability and allow passage to continuous first passage.
-- source:
--   Avram, Palmowski and Pistorius (2007) one-sided stopped exponential argument; Prove2Me accepted general nonnegative uniform-second-moment expectation convergence bef79c38-a4aa-42be-b897-fd1baeed7998, newly Proved second-moment estimate 3d273a9d-d6cd-42e5-bc2a-89e7e5558b95, and proposed square integrability 537b7855-7bf3-4c48-8ed6-109fca99c2a7 (must be Proved before publishing this dependent statement).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_reserve_time_measurable
import Theorems.Thm_AvramDividend_Classical_levy_capped_upcrossing_compensated_exp_second_moment_bound
import Theorems.Thm_AvramDividend_Classical_levy_capped_upcrossing_compensated_exp_square_integrable
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment
import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_capped_upper_grid_exp_expectation_of_ae_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℕ → ℝ≥0)
    (hc : ∀ n, Monotone (clock n)) (hc0 : ∀ n, clock n 0 = 0)
    (H : ℕ → Filtration ℕ mΩ)
    (hH : ∀ n k, H n k = 𝓕 (clock n k))
    (θ : ℝ) (hθ : 0 ≤ θ) (z : ℝ) (m : ℕ → ℕ)
    (N : ℝ≥0) (hNm : ∀ n, clock n (m n) ≤ N)
    (Z : Ω → ℝ) (hZm : AEStronglyMeasurable Z P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n =>
      let K := hittingBtwn (fun k η => X.X (clock n k) η) (Ioi z) 0 (m n) ω
      Real.exp (θ * X.X (clock n K) ω - (clock n K : ℝ) * X.ψ θ))
      atTop (𝓝 (Z ω))) :
    Integrable Z P ∧ Tendsto (fun n => ∫ ω,
      let K := hittingBtwn (fun k η => X.X (clock n k) η) (Ioi z) 0 (m n) ω
      Real.exp (θ * X.X (clock n K) ω - (clock n K : ℝ) * X.ψ θ) ∂P)
      atTop (𝓝 (∫ ω, Z ω ∂P)) := by sorry
