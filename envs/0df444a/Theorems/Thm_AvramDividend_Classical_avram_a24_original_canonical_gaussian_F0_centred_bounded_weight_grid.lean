-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_gaussian_F0_centred_bounded_weight_grid
-- name    : AvramDividend.Classical.avram_a24_original_canonical_gaussian_F0_centred_bounded_weight_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:49:40.677803+00:00
-- url     : https://prove2.me/theorems/0747b846-5b3e-4f81-ad55-3e73e7addfd3
-- title:
--   Exact original clipped uniform Gaussian finite-mesh martingale source centred at F0
-- statement:
--   For every original zero-jump Gaussian Levy surplus and actual deterministic-horizon bounded stopping time, take the exact canonical clipped physical uniform grid. If gradient and Hessian weights at those genuine stopped clock starts are measurable with respect to the corresponding stopped histories, strongly measurable and almost-everywhere bounded, then the sum of their original drift-centred linear Gaussian increments and variance-compensated quadratic Gaussian increments is integrable and has conditional expectation zero at the initial filtration. Both cell first and second moments are supplied automatically by the previously kernel-proved exact canonical grid theorem. This establishes a true physical finite-mesh centred source needed to prove the original A24 finite-cap reward upper bound; the hard Ito-Stieltjes chain-rule L1 limit remains independent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_gaussian_grid_joint_stop_and_horizon
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_clipped_gaussian_grid_conditional_first_second_moments
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_stopped_gaussian_physical_grid_F0_centred
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a24_original_canonical_gaussian_F0_centred_bounded_weight_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (n : ℕ) (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    ∀ j : ℕ,
      let δ : ℝ≥0 := (n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
      let S : Finset ℕ := Finset.range (j + 1)
      let τg : ℕ → Ω → ℝ≥0 := fun i ω =>
        min ((i : ℝ≥0) * δ) (σ ω)
      ∀ (hτg : ∀ i ∈ S, ∀ s : ℝ≥0,
          MeasurableSet[𝓕.rightCont s] {ω : Ω | τg i ω ≤ s})
        (G H : ℕ → Ω → ℝ)
        (hGm : ∀ i (hi : i ∈ S),
          Measurable[(isStoppingTime_withTop_of_le_events (τg i)
            (hτg i hi)).measurableSpace] (G i))
        (hHm : ∀ i (hi : i ∈ S),
          Measurable[(isStoppingTime_withTop_of_le_events (τg i)
            (hτg i hi)).measurableSpace] (H i))
        (hGAE : ∀ i ∈ S, AEStronglyMeasurable (G i) P)
        (hHAE : ∀ i ∈ S, AEStronglyMeasurable (H i) P)
        (BG BH : ℕ → ℝ)
        (hGB : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖G i ω‖ ≤ BG i)
        (hHB : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ BH i),
      let M : ℕ → Ω → ℝ := fun i ω =>
        X.X (τg i ω + δ) ω - X.X (τg i ω) ω - (δ : ℝ) * X.c
      let Q : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (G i ω * M i ω +
          (H i ω * (M i ω)^2 - (δ : ℝ) * X.σ^2 * H i ω))
      Integrable Q P ∧
      condExp (𝓕.rightCont 0) P Q =ᵐ[P] (fun _ => (0 : ℝ)):= by sorry
