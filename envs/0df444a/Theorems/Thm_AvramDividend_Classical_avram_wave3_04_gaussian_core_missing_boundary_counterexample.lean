-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_core_missing_boundary_counterexample
-- name    : AvramDividend.Classical.avram_wave3_04_gaussian_core_missing_boundary_counterexample
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:20:57.163887+00:00
-- url     : https://prove2.me/theorems/c6ea4572-1757-4c26-852c-8ef5e6b15a5d
-- title:
--   Gaussian unbounded-variation stochastic core has all hypotheses but violates its claimed reward bound
-- statement:
--   Fix a Gaussian spectrally negative Levy process with positive Gaussian coefficient, zero jump measure and drift -1, and any initial reserve between zero and one. The zero-extended affine candidate w(y)=y-1 on y>=0 satisfies every analytic premise of the canonical UBV verification core at discount q=1, cap infinity. The zero-barrier policy plus a unit linear drain is an admissible dividend strategy; its strictly positive-time terminal nonnegativity requirement is vacuous because ruin occurs at time zero pathwise, and all active right dividend jumps satisfy the prescribed drop bound. Yet its initial Stieltjes atom pays x>0 while w(x)<=0, contradicting the canonical upper bound at every nonnegative horizon. This conditional source-level refutation uses existing remotely Proved helper theorems and identifies the omitted w(0)>=0 assumption from the paper.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), especially w(0)>=0; Prove2Me accepted Gaussian analytic package 6faf6869-3bfa-4053-9072-3814eb785f5a and drained pathwise counterexample 9d21e277-1af0-4e10-8404-edde635085f6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_gaussian_cutoff_canonical_analytic_hypotheses
import Theorems.Thm_AvramDividend_Classical_drained_strategy_core_pathwise_premises_and_bound_violation

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_gaussian_core_missing_boundary_counterexample
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
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ⊤} ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < ⊤ →
        X.GeneratorIntegrable w y ∧
          X.generator w y - (1 : ℝ) * w y ≤ 0) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < ⊤ →
        1 ≤ deriv w y)) ∧
    ENNReal.ofReal x ≤ (⊤ : ℝ≥0∞) ∧
    IsAdmissibleLe X x ⊤ D ∧
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
