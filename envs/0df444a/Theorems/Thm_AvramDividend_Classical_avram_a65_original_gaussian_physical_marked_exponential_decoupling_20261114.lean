-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a65_original_gaussian_physical_marked_exponential_decoupling_20261114
-- name    : AvramDividend.Classical.avram_a65_original_gaussian_physical_marked_exponential_decoupling_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T12:46:25.975969+00:00
-- url     : https://prove2.me/theorems/2e8107c5-c875-4d58-a5ca-58c0f8617825
-- title:
--   Original finite-jump Gaussian residual and causal physical marks: independent exponential factors with source and marked Poisson Laplace balances
-- statement:
--   On the actual original filtered finite-negative-activity spectrally negative Levy source, separate the intrinsic residual from the causal finite marked jump sum. For each positive time and positive exponential tilt construct measurable real versions of these random variables, independent exponential factors, integrability of the source product and negative jump factor, the exact two exponential moment formulae, and their sigma-square Gaussian exponent cancellation. The child isolates the genuine Levy-Ito source/marked jump independence and Poisson Laplace computation. It neither assumes nor constructs a Gaussian companion on another probability space.
-- source:
--   Avram–Palmowski–Pistorius (2007), Lévy-Khintchine finite-activity decomposition; existing Proved 6366b3de actual physical jump sum identity, def7cb73 physical source exponential product, 640eca5f finite causal mark factor, 4c568d5d independent integrable product, 8d8a562e Gaussian exponent cancellation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a65_original_gaussian_physical_marked_exponential_decoupling_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ) (hNu : X.ν ≠ 0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ (t : ℝ≥0) (ht : 0 < t) (θ : ℝ), 0 < θ →
      ∃ (H J : Ω → ℝ) (a b : ℝ),
        Measurable H ∧ Measurable J ∧
        (H =ᵐ[P] R t) ∧
        (J =ᵐ[P] fun ω =>
          ∑' u : ℝ≥0,
            if 0 < u ∧ u ≤ t then
              X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
            else 0) ∧
        IndepFun (fun ω => Real.exp (θ * H ω))
          (fun ω => Real.exp (θ * J ω)) P ∧
        Integrable (fun ω => Real.exp (θ * (H ω + J ω))) P ∧
        Integrable (fun ω => Real.exp (θ * J ω)) P ∧
        (∫ ω, Real.exp (θ * (H ω + J ω)) ∂P) = Real.exp a ∧
        (∫ ω, Real.exp (θ * J ω) ∂P) = Real.exp b ∧
        a - b = (t : ℝ) * (X.σ ^ 2 * θ ^ 2 / 2) := by sorry
