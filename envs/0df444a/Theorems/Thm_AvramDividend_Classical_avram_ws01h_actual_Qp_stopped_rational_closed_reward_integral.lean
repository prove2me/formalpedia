-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_stopped_rational_closed_reward_integral
-- name    : AvramDividend.Classical.avram_ws01h_actual_Qp_stopped_rational_closed_reward_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:22:44.586332+00:00
-- url     : https://prove2.me/theorems/15cf1a00-24bb-460e-890f-4732831ae4e0
-- title:
--   Genuine terminally tilted Qp killed stopped-history rational-grid and closed continuous shifted-future rewards have exactly equal masses
-- statement:
--   At any measurable finite nonnegative random record age τ of the actual spectrally negative Lévy process, and for any measurable killed-prefix event A, the true terminally tilted original-law Esscher path×real Exp(p) joint integral of the stopped event τ≤r and every rational shifted-future reserve test at ages k/n before r−τ coincides exactly with the joint integral of the same killed historical event and genuine complete continuous closed shifted-future nonruin from reserve a through the residual horizon. Both events are jointly measurable in original path and clock; on each realised sample path, the accepted actual-clock translation of rational/closed future survival ensures equality for Lebesgue-a.e. observation age, preserved under the true Qp likelihood by accepted a.e. transfer. No scale-exit quotient, fictitious tilted infinite-path law or uncountable path evaluation measurability assumption is used. This is the key source-level identification of the record branch in the finite Esscher CDF renewal.
-- source:
--   Proved genuine Qp per-path a.e. transfer 660148a3 (candidate 18431); shifted actual clock rational/closed a.e. 09590602 (18430); random stopped closed future joint measurability 844b8089 (18433); accepted whole shifted path measurable 8e59a363 and rational future reward measurable 0b7edea5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_genuine_Qp_pathwise_volume_ae_reward_transfer
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_random_record_shifted_rational_survival_ae_clock
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_stopped_future_closed_survival_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_rational_age_fullPath_survival_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01h_actual_Qp_stopped_rational_closed_reward_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (a : ℝ) (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (A : Set Ω) (hA : MeasurableSet A) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     let Bgrid : Set (Ω × ℝ) := {z |
       (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
       ∀ n : ℕ, 0 < n → ∀ k : ℕ,
         (k : ℝ≥0) * (n : ℝ≥0)⁻¹ <
           Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
         0 ≤ a + (X.X (τ z.1 + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) z.1 -
           X.X (τ z.1) z.1)}
     let Bfull : Set (Ω × ℝ) := {z |
       (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
       ∀ u : ℝ≥0, u ≤ Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
         0 ≤ a + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)}
     (∫⁻ z, Bgrid.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp) =
     (∫⁻ z, Bfull.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp)) := by sorry
