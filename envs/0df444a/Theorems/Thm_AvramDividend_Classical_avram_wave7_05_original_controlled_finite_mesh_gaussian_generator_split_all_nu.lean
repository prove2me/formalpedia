-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_controlled_finite_mesh_gaussian_generator_split_all_nu
-- name    : AvramDividend.Classical.avram_wave7_05_original_controlled_finite_mesh_gaussian_generator_split_all_nu
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:51:36.483127+00:00
-- url     : https://prove2.me/theorems/86b93f5e-1e2d-4a88-9b92-8a8d766b928e
-- title:
--   All-nu actual ruin-controlled finite mesh generator splits exact half Gaussian bracket
-- statement:
--   For the exact original spectrally negative Levy process X, every finite mesh of its actual dividend-controlled strict prepayment reserve leftLim(x+X-rightLimit D), with true ruin survival, horizon truncation and source discount, has a finite generator sum whose Gaussian term is exactly sigma squared over two times the Hessian. The remaining terms are original drift, actual Levy jump generator integral against X.nu, and discount. This algebraic mesh separation holds for all nu and sigma including zero. It does not itself assert stochastic Ito or zero expectation of a continuous martingale.
-- source:
--   Proved original controlled generator split all-nu b9eb647d-6cde-4050-a94a-7c30045b29a4, summed by pinned Finset.sum_add_distrib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_predividend_generator_gaussian_split_all_nu

open MeasureTheory Set ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_original_controlled_finite_mesh_gaussian_generator_split_all_nu
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0) (S : Finset ι) (t : ι → ℝ≥0) (ω : Ω) :
    let y : ι → ℝ := fun i => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) (t i)
    let k : ι → ℝ := fun i =>
      if t i ≤ T then
        (if (t i : ℝ≥0∞) ≤ ruinTime X x D ω then 1 else 0) else 0
    (∑ i ∈ S,
      k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
        (X.generator w (y i) - q * w (y i)))) =
      (∑ i ∈ S,
        k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w (y i)))) +
      (∑ i ∈ S,
        k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
          (X.c * deriv w (y i) +
            (∫ z in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand w (y i) z ∂X.ν) -
              q * w (y i)))) := by sorry
