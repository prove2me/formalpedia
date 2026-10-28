-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_capped_firstRecord_exp_clock_fullPath_esscher_mixture
-- name    : AvramDividend.Classical.avram_ws01e_b_capped_firstRecord_exp_clock_fullPath_esscher_mixture
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T11:33:15.973368+00:00
-- url     : https://prove2.me/theorems/03d9a16f-745e-4405-8365-3c0755dec426
-- title:
--   Full future-path Esscher reward integrated over the genuine Exp(p) residual age at censored first records
-- statement:
--   For the genuine uncensored capped first upper record of the spectrally negative Levy process, every measurable full future-path reward family H(u,path), with explicitly measurable integrated fresh-side clock kernel, has a genuine Exp(p) clock mixture Esscher factorisation. The integral over real exponential-clock ages of historical discount times post-record compensated Esscher factor and H equals the uncensored stopped discount mass times the complete real-clock mixture of the original fresh-path deterministic-age Esscher marginal. This integrates every lag of the verified first-record whole-future-path factor under the actual real Exp(p) measure, without assuming a globally tilted infinite-path product law; the final variable clock-shift and prefix-likelihood normalisation remain separate.
-- source:
--   Fubini/ENNReal lintegral constant factoring plus accepted actual capped first-record full shifted path Esscher factor 393e588c-5827-4f8a-acb1-f1d492008ce9, instantiated for every residual clock age r.toNNReal and section reward H(r.toNNReal,·). Exact outer real clock is expMeasure p, and hRMeas is the explicit kernel measurability condition required by lintegral_const_mul.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_capped_firstRecord_full_futurePath_esscher_reward_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_capped_firstRecord_exp_clock_fullPath_esscher_mixture
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (N : ℝ≥0)
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
         {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
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
       {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
     (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P)) * (∫⁻ r : ℝ, (∫⁻ ω,
       ENNReal.ofReal (Real.exp
         (θ * X.X (Real.toNNReal r) ω -
           (Real.toNNReal r : ℝ) * X.ψ θ)) *
        H (Real.toNNReal r) (fun t : ℝ≥0 => X.X t ω) ∂P) ∂(expMeasure p)) := by sorry
