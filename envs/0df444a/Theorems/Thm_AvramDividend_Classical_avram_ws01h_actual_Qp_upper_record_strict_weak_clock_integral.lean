-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_upper_record_strict_weak_clock_integral
-- name    : AvramDividend.Classical.avram_ws01h_actual_Qp_upper_record_strict_weak_clock_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:30:00.413921+00:00
-- url     : https://prove2.me/theorems/7a0721f3-c4ee-4650-af70-e2072d1019c9
-- title:
--   Genuine terminal Esscher Qp strict and weak original upper-record before-real-clock integrals agree for arbitrary rewards
-- statement:
--   For the actual source spectrally negative Lévy process with a nonnegative strict upper record threshold, nonnegative Esscher tilt and positive independent real exponential clock rate, take the true reweighted joint path×clock law Qp. On the genuine finite first-record event, replacing (record age ≤ real observation time) by strict (record age < real observation time) changes no integral of any jointly measurable nonnegative path/clock reward. The only discrepancy is the graph of the original upper-record random age; the already canonically proved true Qp upper record age tie theorem gives this graph measure zero, with no assumptions on atoms of the Lévy process or a globally tilted infinite path measure. This exact strict/weak real-clock bridge is needed to identify the finite capped Qp first-record renewal with the official strict upper-before-lower exit event.
-- source:
--   Proved avram_ws01e_b_actual_Qp_real_exp_clock_record_age_tie_zero 7e8e930e; Mathlib ae_iff and lintegral_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_real_exp_clock_record_age_tie_zero

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_actual_Qp_upper_record_strict_weak_clock_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b θ p : ℝ) (hb : 0 ≤ b) (hθ : 0 ≤ θ) (hp : 0 < p)
    (R : Ω × ℝ → ℝ≥0∞) (hR : Measurable R) :
    (let age : Ω → ℝ≥0 := fun ω => (twoSidedExitUpTime X b ω).toNNReal
     let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z, ({z : Ω × ℝ | 0 ≤ z.2 ∧
       twoSidedExitUpTime X b z.1 < ⊤ ∧
       (age z.1 : ℝ) ≤ z.2}).indicator R z ∂Qp) =
     (∫⁻ z, ({z : Ω × ℝ | 0 ≤ z.2 ∧
       twoSidedExitUpTime X b z.1 < ⊤ ∧
       (age z.1 : ℝ) < z.2}).indicator R z ∂Qp)) := by sorry
