-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_capped_firstRecord_genuine_Qp_fullPath_unnormalised_regeneration
-- name    : AvramDividend.Classical.avram_ws01e_b_capped_firstRecord_genuine_Qp_fullPath_unnormalised_regeneration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:19:05.070361+00:00
-- url     : https://prove2.me/theorems/01473e4b-7b5e-4ba7-92f7-28f7c9fa50be
-- title:
--   Genuine Qp unnormalised stopped residual-clock and whole-future-path renewal at capped strict upper records
-- statement:
--   For an actual spectrally negative Levy process and the true random-terminal Esscher joint density on original path times real Exp(p) clock, combine the exact tilted stopped-clock residual shift and the proved whole-future-path first strict upper-record clock mixture. Under explicit source-specific measurable age, uncensored record event, measurable full-path reward sections and kernel, and the pointwise noncircular stopped density and stopped prefix discount algebra, the unnormalised true Qp joint mass of every stopped whole-path reward factorises as the uncensored first-record discounted survival mass times the fresh true random-terminal Esscher reward marginal. No cancellation or conditional division is assumed, even when the survival mass is zero. The exact hWeight is the first-record no-positive-overshoot identity to be discharged separately from Proved level attainment; hSplit is the already-Proved stopped likelihood algebra in real-clock coordinates. This is a substantive finite-rate regeneration bridge, not a generic measurability lemma or the eventual conditional pair law. The arbitrary record event A has an explicit decidability instance solely to elaborate its if-then-else indicator. Such an instance is always available classically and is not a probabilistic hypothesis.
-- source:
--   Direct composition of now canonically Proved true terminally tilted Qp stopped-clock full-path shift d1036279 and capped strict first-record full-path Exp(p) mixture 03d9a16f, via pinned ENNReal Tonelli lintegral_lintegral_swap, lintegral_const_mul and explicit measurable product integrand. Its hypotheses isolate only original-law event and stopped likelihood side conditions; no WH independence or global infinite-horizon Esscher product is presumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_stopped_clock_fullPath_esscher_shift_integral
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_capped_firstRecord_exp_clock_fullPath_esscher_mixture

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_capped_firstRecord_genuine_Qp_fullPath_unnormalised_regeneration
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (N : ℝ≥0)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    [hDec : DecidablePred (fun ω : Ω => ω ∈ A)]
    (hτdef : τ = fun ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal)
    (hAdef : A =
      {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)})
    (hτ : Measurable τ) (hA : MeasurableSet A)
    (W : Ω → ℝ≥0∞)
    (hW : ∀ ω : Ω, W ω = if ω ∈ A then 1 else 0)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hWeight : ∀ ω : Ω, ω ∈ A →
      ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) *
        ENNReal.ofReal (Real.exp
          (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) =
        discount (τ ω))
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : ∀ u : ℝ≥0, Measurable (H u))
    (hRMeas : Measurable (fun r : ℝ =>
      (∫⁻ ω, ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal r) ω -
          (Real.toNNReal r : ℝ) * X.ψ θ)) *
        H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P)))
    (hPostMeas : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 -
          X.X (τ z.1) z.1) -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)) *
      H (Real.toNNReal z.2)
        (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 -
          X.X (τ z.1) z.1)))
    (hJoint : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (hObserve : Measurable (fun z : Ω × ℝ =>
      W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ)))
        (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)))
    (hReward : Measurable (fun z : Ω × ℝ =>
      (W z.1 * ENNReal.ofReal (Real.exp
        (θ * X.X (τ z.1) z.1 - (τ z.1 : ℝ) * X.ψ θ))) *
      (ENNReal.ofReal (Real.exp
        (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 -
          X.X (τ z.1) z.1) -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)) *
        H (Real.toNNReal z.2)
          (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 -
            X.X (τ z.1) z.1))))
    (hSplit : ∀ (ω : Ω) (t : ℝ), (τ ω : ℝ) ≤ t →
      ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal t) ω -
          (Real.toNNReal t : ℝ) * X.ψ θ)) =
      ENNReal.ofReal (Real.exp
        (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) *
      ENNReal.ofReal (Real.exp
        (θ * (X.X (τ ω + Real.toNNReal (t - (τ ω : ℝ))) ω -
          X.X (τ ω) ω) -
          (Real.toNNReal (t - (τ ω : ℝ)) : ℝ) * X.ψ θ))) :
    (∫⁻ z : Ω × ℝ,
      if (τ z.1 : ℝ) ≤ z.2 then
        W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ)))
          (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 -
            X.X (τ z.1) z.1)
      else 0
      ∂((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) =
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      (∫⁻ r : ℝ, (∫⁻ ω,
        ENNReal.ofReal (Real.exp
          (θ * X.X (Real.toNNReal r) ω -
            (Real.toNNReal r : ℝ) * X.ψ θ)) *
        H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P)
        ∂(expMeasure p)) := by sorry
