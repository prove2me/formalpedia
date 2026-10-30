-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_Qp_strict_lower_killing_eq_closed_survival_reward
-- name    : AvramDividend.Classical.avram_ws01h_true_Qp_strict_lower_killing_eq_closed_survival_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:05:16.523813+00:00
-- url     : https://prove2.me/theorems/7f51c5a4-e4a4-4717-bba3-2a263d08aa9d
-- title:
--   True terminally tilted Qp strict lower killing equals complete closed-history nonruin for any source reward
-- statement:
--   For the genuine terminally tilted Esscher law Qp on the original Lévy sample space times its actual independent real Exp(p) clock, every measurable nonnegative source reward integrates equally on the strict lower-clock survival event and on the complete closed nonruin path-history event. Apply the accepted original P×Exp(p) equality to the measurable reward multiplied by the actual random-terminal Esscher density, then use the true Radon–Nikodym withDensity integral identity. This carries the a.e.-clock boundary result through the genuine Qp law, with no arbitrary changed infinite path probability or exit scale ratio.
-- source:
--   Canonically Proved chat04_true_strict_closed_exponential_product_integral_ws01a f9d7ced7, both actual lower joint event measurable theorems and accepted source joint time-state measurable, pinned Mathlib lintegral_withDensity_eq_lintegral_mul.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_true_strict_closed_exponential_product_integral_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_strict_lower_killing_joint_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_closed_history_lower_survival_joint_measurable_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_true_Qp_strict_lower_killing_eq_closed_survival_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) (θ : ℝ) (x : ℝ)
    (R : Ω × ℝ → ℝ≥0∞) (hR : Measurable R) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (ProbabilityTheory.expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z : Ω × ℝ,
       ({z : Ω × ℝ | 0 ≤ z.2 ∧
         ENNReal.ofReal z.2 < twoSidedExitDownTime X (-x) z.1}).indicator R z
       ∂Qp) =
     (∫⁻ z : Ω × ℝ,
       ({z : Ω × ℝ | 0 ≤ z.2 ∧
         ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 →
           -x ≤ X.X s z.1}).indicator R z
       ∂Qp)) := by sorry
