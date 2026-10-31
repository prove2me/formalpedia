-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_unconditional_gaussian_all_cap_counterexample
-- name    : AvramDividend.Classical.avram_wave3_04_unconditional_gaussian_all_cap_counterexample
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:02:04.077132+00:00
-- url     : https://prove2.me/theorems/33fd15dc-8521-4cd8-9217-0701de90d703
-- title:
--   Concrete Gaussian Lévy law refutes UBV verification at every eligible cap
-- statement:
--   There exists a concrete spectrally negative Gaussian Lévy law on the original Gaussian-limit Brownian probability space such that, for every 0<x<=1, every reserve cap C containing ENNReal.ofReal x, and every nonnegative stopping horizon T, the zero-barrier-plus-unit-continuous-drain dividend strategy and zero-extended affine candidate w(y)=y-1 satisfy all premises of the original UBV dividend verification core but violate its expected discounted Stieltjes dividend upper bound. The process has nonzero Brownian volatility, zero jump measure and a genuine adapted filtration.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), missing hypothesis w(0)>=0; Prove2Me accepted all-cap Gaussian source counterexample UUID f0c20407-30e9-494f-b093-35effb76242b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_concrete_gaussian_levy_source_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_drifted_unit_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_all_cap_core_counterexample

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_unconditional_gaussian_all_cap_counterexample :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (X : SpectrallyNegativeLevy gaussianLimit 𝓕),
      ∀ (x : ℝ), 0 < x → x ≤ 1 →
      ∀ (C : ℝ≥0∞), ENNReal.ofReal x ≤ C →
      ∀ (T : ℝ), 0 ≤ T →
    let w : ℝ → ℝ := fun z => if z < 0 then 0 else z - 1
    let D : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
      fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)
    (X.Standing ∧ ¬ X.BoundedVariation ∧
      ContinuousOn w (Ici 0) ∧
      (∀ y : ℝ, y < 0 → w y = 0) ∧
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        X.GeneratorIntegrable w y ∧
          X.generator w y - (1 : ℝ) * w y ≤ 0) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        1 ≤ deriv w y)) ∧
    IsAdmissibleLe X x C D ∧
    (∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) ∧
    (∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) ∧
    ¬ ((∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-((1 : ℝ) * t)))
        ∂(dividendMeasure D ω) ∂gaussianLimit) ≤ ENNReal.ofReal (w x)) := by sorry
