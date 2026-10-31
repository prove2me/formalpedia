-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_unconditional_gaussian_finite_cap_counterexample
-- name    : AvramDividend.Classical.avram_wave3_04_unconditional_gaussian_finite_cap_counterexample
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:52:47.263643+00:00
-- url     : https://prove2.me/theorems/3acb926a-cf92-4393-9ec4-f8ab10024d88
-- title:
--   Concrete Gaussian Lévy law refutes finite-cap unbounded-variation dividend verification
-- statement:
--   There exists an actual spectrally negative Gaussian Lévy process on the Gaussian-limit Brownian probability space satisfying the source process, filtration and integrability fields such that for every 0<x<=1 and horizon T>=0 the zero-barrier strategy with unit continuous drain and w(y)=y-1 for y>=0 satisfies the full premises of the canonical UBV finite-cap C=1 stochastic verification core, yet violates its expected discounted dividend bound. The cap is genuinely finite, and the source Stieltjes measure includes both the initial right jump and diffuse subsequent dividend control.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), boundary assumption w(0)>=0 omitted in the canonical formalisation; source Brownian witness and remotely compiled finite-cap Gaussian counterexample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_concrete_gaussian_levy_source_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_drifted_unit_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_finite_cap_core_counterexample

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_unconditional_gaussian_finite_cap_counterexample :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (X : SpectrallyNegativeLevy gaussianLimit 𝓕),
      ∀ (x : ℝ), 0 < x → x ≤ 1 → ∀ (T : ℝ), 0 ≤ T →
    let w : ℝ → ℝ := fun z => if z < 0 then 0 else z - 1
    let D : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
      fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)
    (X.Standing ∧ ¬ X.BoundedVariation ∧
      ContinuousOn w (Ici 0) ∧
      (∀ y : ℝ, y < 0 → w y = 0) ∧
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal (1 : ℝ)} ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal (1 : ℝ) →
        X.GeneratorIntegrable w y ∧
          X.generator w y - (1 : ℝ) * w y ≤ 0) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal (1 : ℝ) →
        1 ≤ deriv w y)) ∧
    ENNReal.ofReal x ≤ ENNReal.ofReal (1 : ℝ) ∧
    IsAdmissibleLe X x (ENNReal.ofReal (1 : ℝ)) D ∧
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
