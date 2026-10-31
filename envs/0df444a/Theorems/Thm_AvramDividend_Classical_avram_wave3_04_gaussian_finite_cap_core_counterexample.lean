-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_finite_cap_core_counterexample
-- name    : AvramDividend.Classical.avram_wave3_04_gaussian_finite_cap_core_counterexample
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:35:12.013244+00:00
-- url     : https://prove2.me/theorems/2d3c6a65-dfa1-4eca-9f05-d4eb0723378d
-- title:
--   Finite-cap Gaussian unbounded-variation verification counterexample
-- statement:
--   For every positive initial capital x<=1 and nonnegative finite horizon T, a spectrally negative Gaussian Lévy process with drift -1, unit volatility and no jump measure, together with candidate w(y)=if y<0 then 0 else y-1 and the zero-barrier dividend strategy plus continuous unit drain, satisfies every hypothesis of the canonical UBV stochastic verification core with the genuinely finite reserve cap C=1. Nevertheless the expected discounted dividend reward exceeds ENNReal.ofReal(w(x)). This demonstrates the missing boundary condition w(0)>=0 in Avram–Palmowski–Pistorius Proposition 4(i) and the need to account for both initial right dividend jumps and diffuse Stieltjes mass.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), w(0)>=0; accepted Prove2Me Gaussian analytic, drained strategy, and pathwise reserve negativity theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_gaussian_cutoff_canonical_analytic_hypotheses
import Theorems.Thm_AvramDividend_Classical_drained_strategy_core_pathwise_premises_and_bound_violation
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_reserve_negative

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_gaussian_finite_cap_core_counterexample
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (hI : Integrable (X.X 1) P) (hν : X.ν = 0) (hc : X.c = -1)
    (x : ℝ) (hx : 0 < x) (hxle : x ≤ 1)
    (T : ℝ) (hT : 0 ≤ T) :
    let w : ℝ → ℝ := fun z => if z < 0 then 0 else z - 1
    let D : ℝ≥0 → Ω → ℝ :=
      fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)
    (X.Standing ∧ ¬ X.BoundedVariation ∧
      ContinuousOn w (Ici 0) ∧
      (∀ y : ℝ, y < 0 → w y = 0) ∧
      ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal (1 : ℝ)} ∧
      (∀ y : ℝ, 0 < y →
        ENNReal.ofReal y < ENNReal.ofReal (1 : ℝ) →
        X.GeneratorIntegrable w y ∧
          X.generator w y - (1 : ℝ) * w y ≤ 0) ∧
      (∀ y : ℝ, 0 < y →
        ENNReal.ofReal y < ENNReal.ofReal (1 : ℝ) →
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
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x)) := by sorry
