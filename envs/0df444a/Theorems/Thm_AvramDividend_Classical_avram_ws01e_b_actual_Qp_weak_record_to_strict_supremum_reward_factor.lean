-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_weak_record_to_strict_supremum_reward_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_Qp_weak_record_to_strict_supremum_reward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:57:43.321511+00:00
-- url     : https://prove2.me/theorems/0b0b1124-0418-4372-9290-9e40ac90d4af
-- title:
--   True Esscher real-clock weak upper-record factor transfers to strict supremum threshold without clock ties
-- statement:
--   For the actual spectrally negative Lévy process and true Esscher tilted path plus independent real Exp(p) clock, suppose an arbitrary nonnegative terminal reward W has been proved to factor on the finite weak first strict-upper-record-before-or-at-clock event E. Then the same exact Qp factor holds for the actual strictly exceeded running-supremum threshold S_e>b. This uses the source-specific strict crossing event equivalence and the independently proved Qp nullity of the exact real-clock/record-age equality graph. The weak factor is a supplied previously proved premise; no strict factor or independence is assumed.
-- source:
--   Canonical b626324c pathwise strict supremum/upcrossing equivalence; actual Esscher real Exp clock record tie null theorem; pinned Mathlib Measure.restrict_congr_set and measure_zero_iff_ae_nmem; KKR (2013) §2.1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_Qp_weak_record_to_strict_supremum_reward_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (b : ℝ) (hb : 0 ≤ b)
    (W : Ω × ℝ → ℝ≥0∞)
    (hWeakFactor :
      (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
       let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
       let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}
       let Qp : Measure (Ω × ℝ) :=
         (P.prod (ProbabilityTheory.expMeasure p)).withDensity
           (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
             (θ * X.X (Real.toNNReal z.2) z.1 -
               (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
       (∫⁻ z in E, W z ∂Qp) =
         Qp E * (∫⁻ z : Ω × ℝ, W z ∂Qp))) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (ProbabilityTheory.expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     let A : Set (Ω × ℝ) := {z |
       b < runningSup X (Real.toNNReal z.2) z.1}
     (∫⁻ z in A, W z ∂Qp) =
       Qp A * (∫⁻ z : Ω × ℝ, W z ∂Qp)) := by sorry
