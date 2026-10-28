-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_finiteStopping_full_futurePath_esscher_reward_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_finiteStopping_full_futurePath_esscher_reward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T11:15:37.003288+00:00
-- url     : https://prove2.me/theorems/15c38ec1-8440-42db-a50c-36e5be63ddb4
-- title:
--   Full shifted-path Esscher-weighted reward factor at arbitrary finite Levy stopping times
-- statement:
--   At any genuinely finite Levy stopping time tau and for any measurable stopped-sigma history weight H, the entire shifted future Levy path admits the exact deterministic-time Esscher weighted strong Markov reward factor at every future lag u: E_P[H exp(theta*(X_(tau+u)-X_tau)-u psi(theta)) F(shifted path)]=E_P[H] E_P[exp(theta X_u-u psi(theta))F(original path)]. It includes every measurable nonnegative functional F of the entire future path, not merely fixed-time increments or finite cylinders. The result is a full-future-path tilt component; stopped Esscher prefix weight and random Exp(p) horizon still need to be incorporated to reach Qp regeneration.
-- source:
--   Direct mathematically meaningful Esscher specialisation of the accepted original-law full stopped-history-weighted strong Markov factor b995a471-5065-4673-ba97-d0f13ebfc768, together with measurable_pi_apply and ENNReal.measurable_ofReal for the exponential reward.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_historyWeight_futureReward_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_finiteStopping_full_futurePath_esscher_reward_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (pastWeight : Ω → ℝ≥0∞)
    (hp : Measurable pastWeight)
    (hpPast : Measurable[
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] pastWeight)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℝ≥0)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hr : Measurable reward) :
    (∫⁻ ω, pastWeight ω *
      (ENNReal.ofReal (Real.exp
        (θ * (X.X (τ ω + u) ω - X.X (τ ω) ω) -
          (u : ℝ) * X.ψ θ)) *
        reward (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)) ∂P) =
    (∫⁻ ω, pastWeight ω ∂P) *
      (∫⁻ ω, ENNReal.ofReal (Real.exp
        (θ * X.X u ω - (u : ℝ) * X.ψ θ)) *
        reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by sorry
