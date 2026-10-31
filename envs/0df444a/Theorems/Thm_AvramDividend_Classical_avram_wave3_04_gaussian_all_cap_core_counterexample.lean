-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_all_cap_core_counterexample
-- name    : AvramDividend.Classical.avram_wave3_04_gaussian_all_cap_core_counterexample
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:56:51.24754+00:00
-- url     : https://prove2.me/theorems/f0c20407-30e9-494f-b093-35effb76242b
-- title:
--   Gaussian UBV verification counterexample at every cap containing initial capital
-- statement:
--   For every Gaussian spectrally negative Lévy source with drift -1, volatility positive, zero jump measure and integrable one-step increment, every 0<x<=1, every extended nonnegative reserve cap C satisfying ENNReal.ofReal x<=C, and every nonnegative horizon, the zero-extended affine w(y)=y-1 and admissible zero-barrier-plus-unit-drain strategy satisfy every canonical UBV verification premise, but the discounted dividend inequality fails. This generalises the canonically Proved finite-cap C=1 counterexample to every eligible finite and infinite cap, using independently accepted source analytic, admissibility and right-payment results.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i) omitted w(0)>=0; Prove2Me Proved Gaussian analytic package, infinite-cap source counterexample, and finite or any-cap admissibility theorem UUID 235540e5-fcdc-4a54-b5e4-d9f443b2b815.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_gaussian_cutoff_canonical_analytic_hypotheses
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_core_missing_boundary_counterexample
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_drained_zero_barrier_admissible_any_cap

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_gaussian_all_cap_core_counterexample
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (hI : Integrable (X.X 1) P) (hν : X.ν = 0) (hc : X.c = -1)
    (x : ℝ) (hx : 0 < x) (hxle : x ≤ 1)
    (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (T : ℝ) (hT : 0 ≤ T) :
    let w : ℝ → ℝ := fun z => if z < 0 then 0 else z - 1
    let D : ℝ≥0 → Ω → ℝ :=
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
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x)) := by sorry
