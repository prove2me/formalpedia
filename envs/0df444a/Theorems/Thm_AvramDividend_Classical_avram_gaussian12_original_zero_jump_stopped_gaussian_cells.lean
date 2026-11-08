-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussian12_original_zero_jump_stopped_gaussian_cells
-- name    : AvramDividend.Classical.avram_gaussian12_original_zero_jump_stopped_gaussian_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:36:47.705468+00:00
-- url     : https://prove2.me/theorems/4a4b4e27-0583-4fd1-8ef4-9e53032cff43
-- title:
--   Original zero-jump Levy Gaussian stopped Taylor cells have conditional zero mean without decomposition assumptions
-- statement:
--   In the source X.ν=0 Gaussian finite-cap regime, each integrable weighted original-X compensated Gaussian increment/Taylor quadratic cell has conditional mean zero at its genuine bounded right-continuous stopped history. Specialising f9916aff with its Gaussian copy Y equal to the original X and both Levy jump remainder paths identically zero makes the same-space source decomposition an algebraic identity, eliminating an otherwise difficult extra hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_variable_stops_predictable_taylor_condExp_zero
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussian12_original_zero_jump_stopped_gaussian_cells
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hG : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i)
        (hτ i hi)).measurableSpace] (G i))
    (hH : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i)
        (hτ i hi)).measurableSpace] (H i))
    (M : ι → Ω → ℝ)
    (hM : M = (fun i ω =>
      (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c) -
      (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c)))
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω * M i ω) P)
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S,
      Integrable (fun ω => H i ω * (M i ω) ^ 2) P) :
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * M i ω +
        (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    ∀ i (hi : i ∈ S),
      Integrable (F i) P ∧
        P[F i |
          (isStoppingTime_withTop_of_le_events (τ i)
            (hτ i hi)).measurableSpace] =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
