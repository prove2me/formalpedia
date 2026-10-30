-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_killed_record_exp_clock_fullPath_esscher_mixture
-- name    : AvramDividend.Classical.avram_ws01h_killed_record_exp_clock_fullPath_esscher_mixture
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:06:59.393905+00:00
-- url     : https://prove2.me/theorems/360f404d-3113-435f-91d7-681ebd6fd972
-- title:
--   Genuine Exp(p) mixture of original lower-killed stopped record full-future Esscher factors
-- statement:
--   The original lower-ruin-killed first strict upper record, capped at a finite deterministic horizon, admits a full-future-path Esscher factorisation integrated over the genuine real exponential residual-clock law. Its historical discounted mass multiplies the original Lévy finite-age Esscher fresh-path reward mixture, with no independent-path-space tilt assumption.
-- source:
--   Avram, Palmowski and Pistorius (2007); and accepted true first-record full-path Esscher renewal 03d9a16f with the original lower killed historical event replaced using the new source-specific stopped Markov factor.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_killed_record_fixedTime_esscher_future_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_killed_record_exp_clock_fullPath_esscher_mixture
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower b : ℝ) (N : ℝ≥0)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : ∀ u : ℝ≥0, Measurable (H u))
    (hRMeas : Measurable (fun r : ℝ =>
      (∫⁻ ω, ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal r) ω -
          (Real.toNNReal r : ℝ) * X.ψ θ)) *
        H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P))) :
    (∫⁻ r : ℝ,
      (let τ : Ω → ℝ≥0 := fun ω =>
         (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
       let A : Set Ω :=
         {ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
         {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
       (∫⁻ ω, if ω ∈ A then discount (τ ω) *
         (ENNReal.ofReal (Real.exp
           (θ * (X.X (τ ω + Real.toNNReal r) ω - X.X (τ ω) ω) -
             (Real.toNNReal r : ℝ) * X.ψ θ)) *
          H (Real.toNNReal r) (fun t : ℝ≥0 =>
            X.X (τ ω + t) ω - X.X (τ ω) ω))
         else 0 ∂P)) ∂(expMeasure p)) =
      (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
       {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
     (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P)) *
       (∫⁻ r : ℝ, (∫⁻ ω,
       ENNReal.ofReal (Real.exp
         (θ * X.X (Real.toNNReal r) ω -
           (Real.toNNReal r : ℝ) * X.ψ θ)) *
         H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P)
       ∂(expMeasure p)) := by sorry
