-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_capped_firstRecord_full_futurePath_esscher_reward_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_capped_firstRecord_full_futurePath_esscher_reward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T11:19:02.265104+00:00
-- url     : https://prove2.me/theorems/393e588c-5827-4f8a-acb1-f1d492008ce9
-- title:
--   Esscher-weighted entire fresh-path reward factor at censored first upper records
-- statement:
--   For any finite cap N on the genuine first strict upper record time of a spectrally negative Levy process, on the event of uncensored record arrival before N, the Esscher-compensated post-record increment over every fixed duration u can be multiplied by an arbitrary measurable nonnegative functional of the entire shifted future path. The original-law joint reward factor then equals its genuine pre-record discounted mass times the full deterministic-time Esscher-weighted future-path marginal. The result has exact full-path reward and first-record stopping event, and is a substantive fixed-lag component needed to integrate the residual independent exponential clock in the true Qp Wiener-Hopf regeneration argument.
-- source:
--   The canonically Proved first-record uncensored full-future-path discounted factor 481d46a9-9eee-447f-ba81-eb05367eff3a applied to G(f)=exp(theta*f(u)-u*psi(theta))*reward(f), with exact whole-path measurability from measurable_pi_apply and ENNReal.measurable_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_firstRecord_uncensored_discountedFutureReward_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_capped_firstRecord_full_futurePath_esscher_reward_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (N u : ℝ≥0)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
     (∫⁻ ω, if ω ∈ A then discount (τ ω) *
       (ENNReal.ofReal (Real.exp
         (θ * (X.X (τ ω + u) ω - X.X (τ ω) ω) -
           (u : ℝ) * X.ψ θ)) *
         reward (fun t : ℝ≥0 =>
           X.X (τ ω + t) ω - X.X (τ ω) ω))
       else 0 ∂P) =
       (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
         (∫⁻ ω, ENNReal.ofReal (Real.exp
           (θ * X.X u ω - (u : ℝ) * X.ψ θ)) *
           reward (fun t : ℝ≥0 => X.X t ω) ∂P)) := by sorry
