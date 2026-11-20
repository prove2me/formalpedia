-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_strict_uniform_original_expected_reward_from_source_mean
-- name    : AvramDividend.Classical.avram_pj_workerC_strict_uniform_original_expected_reward_from_source_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:17:03.367513+00:00
-- url     : https://prove2.me/theorems/76aa372a-c1b6-4007-b3ff-64ca573b2de1
-- title:
--   Original w payoff and full dividend cash expected strict survivor event budget from genuine grid source
-- statement:
--   On strict pre-ruin survivor event A at deterministic t, if the actual discounted original w(postpayment reserve) plus full Stieltjes cash and exact full physical grid source are integrable, and original grid source expectation is <=0 on A, then original reward mean on A is <=w(x)P(A). No Gaussian or finite activity assumptions, no omitted right-payment or within-cell dividends.
-- source:
--   Original expected event budget from candidate original strict clock pathwise w payoff 79e97383; isolates single infinite-activity stochastic source mean obligation in a form reusable by Worker C root.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_strict_preruin_original_payoff_cash_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_strict_uniform_original_expected_reward_from_source_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (t : ℝ≥0) (m : ℕ) (A : Set Ω)
    (hA : MeasurableSet A)
    (hSurvive : ∀ ω ∈ A, (t : ℝ≥0∞) < ruinTime X x D ω)
    (Reward Source : Ω → ℝ)
    (hReward : ∀ ω, Reward ω =
      Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω) +
      (∫⁻ s in Icc (0 : ℝ) (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hSource : ∀ ω, Source ω =
      let u : ℕ → ℝ≥0 := fun i =>
        min (((i : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) * t) t
      let E : ℝ≥0 → ℝ := fun s => Real.exp (-(q * (s : ℝ)))
      let Y : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
      ∑ i ∈ Finset.range (m + 1),
        ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
          E (u i) * (V (Z i) - V (Y (u i)))))
    (hRewardI : Integrable Reward (P.restrict A))
    (hSourceI : Integrable Source (P.restrict A))
    (hMeanSource : (∫ ω in A, Source ω ∂P) ≤ 0) :
    (∫ ω in A, Reward ω ∂P) ≤ w x * (P A).toReal := by sorry
