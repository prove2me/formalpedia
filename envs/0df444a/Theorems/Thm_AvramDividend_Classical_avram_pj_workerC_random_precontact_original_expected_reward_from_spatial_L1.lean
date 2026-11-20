-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_random_precontact_original_expected_reward_from_spatial_L1
-- name    : AvramDividend.Classical.avram_pj_workerC_random_precontact_original_expected_reward_from_spatial_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:21:42.781545+00:00
-- url     : https://prove2.me/theorems/a152c9c5-4edc-4bec-9bd7-b2b0b90ad4c3
-- title:
--   Original random stopping clock strict-survivor expected paid w reward controlled by spatial Lévy source mean plus tolerance
-- statement:
--   On any measurable survivor event A and arbitrary random clock rho with rho(omega)<ruin on A, original discounted w(postpayment reserve) and the full inclusive Stieltjes dividends up to rho have mean ≤w(x)P(A)+ε whenever the genuine rho-clipped uniform physical-grid nonlinear Lévy spatial source has expected value ≤ε. This retains initial 0-clock payment, removes already-proved adverse discount and dividend variation, and avoids assuming finite negative-jump intensity or sigma>0.
-- source:
--   Pointwise original spatial cash envelope 83e5d93d instantiated at each original random rho(omega), then restrict to A and integrate. Exactly isolates the remaining compensated infinite-activity spatial source mean as the only stochastic input for Worker C.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_preruin_original_cash_le_nonlinear_spatial_gain
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_random_precontact_original_expected_reward_from_spatial_L1
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
      (∫⁻ s in Icc (0 : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hSource : ∀ ω, Source ω =
      let u : ℕ → ℝ≥0 := fun i =>
        min (((i : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) * ρ ω) (ρ ω)
      let E : ℝ≥0 → ℝ := fun s => Real.exp (-(q * (s : ℝ)))
      let Y : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
      ∑ i ∈ Finset.range (m + 1),
        E (u i) * (V (Z i) - V (Y (u i))))
    (hRewardI : Integrable Reward (P.restrict A))
    (hSourceI : Integrable Source (P.restrict A))
    (ε : ℝ) (hMeanSource : (∫ ω in A, Source ω ∂P) ≤ ε) :
    (∫ ω in A, Reward ω ∂P) ≤ w x * (P A).toReal + ε := by sorry
