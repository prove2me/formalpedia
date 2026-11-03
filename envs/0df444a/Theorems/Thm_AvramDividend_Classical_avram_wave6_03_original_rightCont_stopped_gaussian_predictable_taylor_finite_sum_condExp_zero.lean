-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_finite_sum_condExp_zero
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_finite_sum_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:38:15.887047+00:00
-- url     : https://prove2.me/theorems/01f8f1b2-f954-4558-9538-dbc7a383ba00
-- title:
--   Finite family of same-source right-continuous stopped Gaussian predictable Taylor residuals is L1 and conditionally mean zero
-- statement:
--   For the original same-sample-path spectrally negative Levy source with zero jump measure and arbitrary Gaussian parameter including sigma zero, let tau be one bounded right-continuous stopping time. For any finite set of future cell lengths h_i and stopped-history measurable gradient and Hessian coefficients G_i,H_i with explicitly integrable weighted source increments and source squares, the sum over i of G_i Delta M_i + H_i[(Delta M_i)^2-sigma^2 h_i] is integrable and has conditional expectation zero given the very same stopped source history. No assumption of independence between overlapping future cells is made: the result follows from stopped martingale-difference conditional identities and finite additivity. This is a finite-source Taylor residual interface, not a standalone Brownian model or a general-jump Ito decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_residual_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_finite_sum_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hG : ∀ i ∈ S,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (G i))
    (hH : ∀ i ∈ S,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (H i))
    (hGI : ∀ i ∈ S, Integrable (fun ω =>
      G i ω * (X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c)) P)
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S, Integrable (fun ω =>
      H i ω * (X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c) ^ 2) P) :
    let Y : ι → Ω → ℝ := fun i ω =>
      X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * Y i ω +
        (H i ω * Y i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
      P[(fun ω => ∑ i ∈ S, F i ω) |
          (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by
  sorry
