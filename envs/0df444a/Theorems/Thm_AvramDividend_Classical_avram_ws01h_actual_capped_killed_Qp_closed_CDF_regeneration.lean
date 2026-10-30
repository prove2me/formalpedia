-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_capped_killed_Qp_closed_CDF_regeneration
-- name    : AvramDividend.Classical.avram_ws01h_actual_capped_killed_Qp_closed_CDF_regeneration
-- status  : Open
-- author  : @WillR
-- created : 2026-10-29T16:32:39.939001+00:00
-- url     : https://prove2.me/theorems/996fe894-4f83-4668-9c9c-3a1805702a5e
-- title:
--   True original lower-killed capped first-record Qp mass factors into the actual original stopped discount and complete Esscher closed-survival CDF
-- statement:
--   For any genuine spectrally negative Lévy process, real Exp(p) terminally Esscher-weighted observation Qp, positive upper gap b, finite record cap N, and arbitrary lower reserve threshold, the actual original lower-killed first-upper-record followed by complete closed shifted-future survival from reserve a, with observation age after τ_N, has exact Qp mass equal to original-P strict lower-killed capped first-record discounted Esscher mass times the true whole-path Esscher Qp lower-survival CDF at a. This is the source-specific stochastic finite-p killed renewal factorisation. Use four independently canonically proved genuine-source identities: rational reward capped true Qp factorisation, source killed-record rational reward as Qp event indicator, Qp stopped rational versus closed full-future a.e. mass, and fresh rational reward equal to complete Esscher CDF. Prove actual τ_N and killed-prefix measurability from original right-continuous stopping-time lemmas. No target two-sided exit ratio, invented changed infinite path-space law or closed-horizon measurability assumption is imported.
-- source:
--   Proved 18434 true capped H factor, 18439 killed rational indicator, 18438 killed stopped rational-to-closed Qp identity (await acceptance), 18422 actual fresh CDF factor; original source upper and lower stoppings.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_capped_killed_Qp_rational_survival_regeneration
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_killed_record_rational_reward_indicator_bridge
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_stopped_rational_closed_reward_integral
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_fresh_rational_Qp_renewal_factor_eq_closed_survival
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_lowerPassage_stopping_rightCont_filtration

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01h_actual_capped_killed_Qp_closed_CDF_regeneration
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower b a : ℝ) (hb : 0 ≤ b) (N : ℝ≥0)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
       {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
     let Bfull : Set (Ω × ℝ) := {z |
       (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
       ∀ u : ℝ≥0, u ≤ Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
         0 ≤ a + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)}
     let discount : ℝ≥0 → ℝ≥0∞ := fun u =>
       ENNReal.ofReal (Real.exp (θ * b - (p + X.ψ θ) * (u : ℝ)))
     let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z, Bfull.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp) =
     (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
       (∫⁻ z, ({z : Ω × ℝ | 0 ≤ z.2 ∧ ∀ s : ℝ≥0,
         s ≤ Real.toNNReal z.2 → 0 ≤ a + X.X s z.1}).indicator
           (fun _ => (1 : ℝ≥0∞)) z ∂Qp)) := by sorry
