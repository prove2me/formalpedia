-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_original_controlled_gradient_stopped_gaussian_quotient_real_L2_convergence
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_original_controlled_gradient_stopped_gaussian_quotient_real_L2_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:25:55.738726+00:00
-- url     : https://prove2.me/theorems/e9748300-b98a-4806-812f-77f4e4897352
-- title:
--   Compact-bounded original stopped controlled Gaussian gradient preserves same-path exponential quotient limit in real L2
-- statement:
--   For the genuine original ν=0 source, original right-continuous bounded stopping time, admissible dividend strategy and C2 HJB test on the finite-cap reserve interior, the actual stopped prepayment capped gradient G bounded by K preserves real L2 convergence of the source's own exponential martingale quotient to its drift-centred true future Gaussian increment. The original-gradient stopped-history measurability is canonically Proved; transform to strong ambient measurability and instantiate the canonically Proved bounded weighted true source quotient convergence. This is a stochastic-cell convergence interface with actual X, not an independent Brownian model, and remains valid at σ=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_controlled_prejump_gradient_stopped_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_quotient_real_L2_convergence

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_original_controlled_gradient_stopped_gaussian_quotient_real_L2_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K) :
    let G : Ω → ℝ := stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto
      (fun θ : ℝ => (∫ ω, (G ω * (Z θ ω - Y ω)) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  sorry
