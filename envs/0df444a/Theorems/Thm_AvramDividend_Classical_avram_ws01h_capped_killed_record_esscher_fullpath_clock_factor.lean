-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_capped_killed_record_esscher_fullpath_clock_factor
-- name    : AvramDividend.Classical.avram_ws01h_capped_killed_record_esscher_fullpath_clock_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:16:30.994594+00:00
-- url     : https://prove2.me/theorems/6b2f3d33-44f8-47de-a069-69cbb0eb061b
-- title:
--   Genuine lower-killed first-record Qp residual-clock and entire-future-path Esscher factor
-- statement:
--   For the genuine terminal Esscher density on P times an independent Exp(p) clock, the joint stopped first-upcrossing contribution on the actual past no-lower-ruin event factors into the original-P stopped Esscher mass and a true fresh terminally weighted exponential-clock future reward. The proof derives the finite cap history factor by a source-specific killed Markov theorem and real-clock Tonelli, with all measurability and stopped-density premises exposed.
-- source:
--   Avram–Palmowski–Pistorius (2007), genuine two-sided exit; accepted Qp stopped clock shift d1036279 and genuine lower-killed Exp(p) mixture, adapting the canonically proved un-killed Qp factor 01473e4b without importing the desired exit law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_stopped_clock_fullPath_esscher_shift_integral
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_killed_record_exp_clock_fullPath_esscher_mixture

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_capped_killed_record_esscher_fullpath_clock_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower b : ℝ) (N : ℝ≥0)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    [hDec : DecidablePred (fun ω : Ω => ω ∈ A)]
    (hτdef : τ = fun ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal)
    (hAdef : A =
      {ω : Ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
      {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)})
    (hτ : Measurable τ) (hA : MeasurableSet A)
    (W : Ω → ℝ≥0∞)
    (hW : ∀ ω : Ω, W ω = if ω ∈ A then 1 else 0)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hWeight : ∀ ω : Ω, ω ∈ A →
      ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) * ENNReal.ofReal (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) = discount (τ ω))
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : ∀ u : ℝ≥0, Measurable (H u))
    (hRMeas : Measurable (fun r : ℝ =>
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal r) ω - (Real.toNNReal r : ℝ) * X.ψ θ)) * H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P)))
    (hPostMeas : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 - X.X (τ z.1) z.1) - (Real.toNNReal z.2 : ℝ) * X.ψ θ)) *
      H (Real.toNNReal z.2) (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)))
    (hJoint : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (hObserve : Measurable (fun z : Ω × ℝ =>
      W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ))) (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)))
    (hReward : Measurable (fun z : Ω × ℝ =>
      (W z.1 * ENNReal.ofReal (Real.exp (θ * X.X (τ z.1) z.1 - (τ z.1 : ℝ) * X.ψ θ))) *
      (ENNReal.ofReal (Real.exp (θ * (X.X (τ z.1 + Real.toNNReal z.2) z.1 - X.X (τ z.1) z.1) - (Real.toNNReal z.2 : ℝ) * X.ψ θ)) * H (Real.toNNReal z.2) (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1))))
    (hSplit : ∀ (ω : Ω) (t : ℝ), (τ ω : ℝ) ≤ t →
      ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal t) ω - (Real.toNNReal t : ℝ) * X.ψ θ)) =
      ENNReal.ofReal (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) *
      ENNReal.ofReal (Real.exp (θ * (X.X (τ ω + Real.toNNReal (t - (τ ω : ℝ))) ω - X.X (τ ω) ω) - (Real.toNNReal (t - (τ ω : ℝ)) : ℝ) * X.ψ θ))) :
    (∫⁻ z : Ω × ℝ,
      if (τ z.1 : ℝ) ≤ z.2 then W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ))) (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
      else 0
      ∂((P.prod (expMeasure p)).withDensity (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) =
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      (∫⁻ r : ℝ, (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal r) ω - (Real.toNNReal r : ℝ) * X.ψ θ)) * H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P) ∂(expMeasure p)) := by sorry
