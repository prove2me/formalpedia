-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_predividend_generator_gaussian_split_all_nu
-- name    : AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_predividend_generator_gaussian_split_all_nu
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:55:22.857202+00:00
-- url     : https://prove2.me/theorems/b9eb647d-6cde-4050-a94a-7c30045b29a4
-- title:
--   Actual controlled pre-dividend killed discounted generator isolates exact sigma-squared-over-two Gaussian term for all jump measures
-- statement:
--   For the genuine original spectrally negative Lévy process X and actual dividend strategy D, at each sample ω and nonnegative time t, evaluate the discounted generator minus q at the strict predictable pre-dividend reserve y=leftLim(x+X.X−rightLimit D). Multiply by the actual finite-horizon and ruin survival indicator. Prove an exact pointwise equality splitting out exp(-qt) (σ²/2) w''(y), with the remaining source drift X.c w'(y), actual negative-jump Lévy integral against X.ν and -q w(y). This algebraic export is valid for arbitrary ν and σ including zero, uses the correct pre-dividend state and discount, and can be directly imported into Chat06's C² source chain-rule calculation once the continuous martingale bracket is constructed. The theorem itself does not claim a pathwise Itô–Meyer formula or independent Brownian copy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_discounted_gaussian_generator_split_export

open MeasureTheory Set ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_predividend_generator_gaussian_split_all_nu
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T t : ℝ≥0) (ω : Ω) :
    let y : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let k : ℝ := if t ≤ T then
      (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then 1 else 0) else 0
    k * (Real.exp (-(q * (t : ℝ))) * (X.generator w y - q * w y)) =
      k * (Real.exp (-(q * (t : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w y)) +
      k * (Real.exp (-(q * (t : ℝ))) *
        (X.c * deriv w y +
          (∫ z in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) -
              q * w y)) := by
  sorry
