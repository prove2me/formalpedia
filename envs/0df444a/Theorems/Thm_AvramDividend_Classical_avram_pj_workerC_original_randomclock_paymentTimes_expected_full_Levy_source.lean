-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_randomclock_paymentTimes_expected_full_Levy_source
-- name    : AvramDividend.Classical.avram_pj_workerC_original_randomclock_paymentTimes_expected_full_Levy_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:27:36.186743+00:00
-- url     : https://prove2.me/theorems/c75d25b9-e9cf-46a2-b179-cc51bfb0d849
-- title:
--   Original random clock inclusive paid dividend cash expected HJB budget from full discounted Lévy source mean
-- statement:
--   Under a measurable event A strictly before actual ruin for any random clock rho, the exact original reward including w(postpayment reserve) discounted and full initial-inclusive paymentTimes∩Iic rho cash has expectation bounded above by w(x)P(A)+epsilon whenever the *combined* full physical-grid HJB source (chronological exponential discount loss plus nonlinear Levy spatial increments) is integrable on A with mean≤epsilon. This is HJB-aligned: does not incorrectly discard negative discount to force a positive spatial mean.
-- source:
--   Proved 79e97383 exact original strict stopped payoff full source, proved bfe4a214 paymentTimes Icc identity, eventwise integration. The remaining source is the original compensated infinite-activity negative-jump HJB time-grid mean estimate, not a Gaussian/finiteactivity assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_strict_preruin_original_payoff_cash_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_randomclock_paymentTimes_expected_full_Levy_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ρ : Ω → ℝ≥0) (m : ℕ) (A : Set Ω)
    (hA : MeasurableSet A)
    (hSurvive : ∀ ω ∈ A, (ρ ω : ℝ≥0∞) < ruinTime X x D ω)
    (Reward Source : Ω → ℝ)
    (hReward : ∀ ω, Reward ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hSource : ∀ ω, Source ω =
      let u : ℕ → ℝ≥0 := fun i =>
        min (((i : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) * ρ ω) (ρ ω)
      let E : ℝ≥0 → ℝ := fun s => Real.exp (-(q * (s : ℝ)))
      let Y : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
      ∑ i ∈ Finset.range (m + 1),
        ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
          E (u i) * (V (Z i) - V (Y (u i)))))
    (hRewardI : Integrable Reward (P.restrict A))
    (hSourceI : Integrable Source (P.restrict A))
    (ε : ℝ) (hMeanSource : (∫ ω in A, Source ω ∂P) ≤ ε) :
    (∫ ω in A, Reward ω ∂P) ≤ w x * (P A).toReal + ε := by sorry
