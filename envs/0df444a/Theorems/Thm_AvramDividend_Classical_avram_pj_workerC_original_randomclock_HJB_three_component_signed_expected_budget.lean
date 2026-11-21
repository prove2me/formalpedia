-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_randomclock_HJB_three_component_signed_expected_budget
-- name    : AvramDividend.Classical.avram_pj_workerC_original_randomclock_HJB_three_component_signed_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:36:07.830684+00:00
-- url     : https://prove2.me/theorems/c8256af7-0180-4231-bf8f-bffc199be111
-- title:
--   Original random stopped full Stieltjes payoff expected bound from centered jump noise, nonpositive HJB drift and integrable small remainder
-- statement:
--   For original random clock rho strictly before ruin on event A, the exact full inclusive dividend cash plus discounted w terminal is bounded in expectation by wx P(A)+epsilon if the full discounted physical-grid Levy source is bounded a.e. by a centered integrable stopped compensated jump martingale M, an integrable nonpositive-mean generator/HJB drift N and an integrable small-mean remainder R. All terms use actual postpayment reserve, full within-cell Stieltjes dividends and original inclusive terminal convention. This is a source-sign certificate that respects the single generator and infinite jump activity.
-- source:
--   Combines the actual full Levy clock+spatial expected budget lemma c75d25b9 with a single centered martingale, signed drift and small remainder. Exact missing mathematical work is the purejump compensated stopped Ito source identification hDom, not assumed Gaussian or finite-activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_randomclock_paymentTimes_expected_full_Levy_source
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_randomclock_HJB_three_component_signed_expected_budget
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
    (M N R : Ω → ℝ)
    (hMI : Integrable M (P.restrict A))
    (hNI : Integrable N (P.restrict A))
    (hRI : Integrable R (P.restrict A))
    (hDom : ∀ᵐ ω ∂(P.restrict A),
      Source ω ≤ (M ω + N ω) + R ω)
    (hMzero : (∫ ω in A, M ω ∂P) = 0)
    (hNneg : (∫ ω in A, N ω ∂P) ≤ 0)
    (ε : ℝ) (hRsmall : (∫ ω in A, R ω ∂P) ≤ ε) :
    (∫ ω in A, Reward ω ∂P) ≤ w x * (P A).toReal + ε := by sorry
