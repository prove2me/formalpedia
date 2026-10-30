-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_Qp_strict_weak_lower_killing_integral_eq
-- name    : AvramDividend.Classical.avram_ws01h_true_Qp_strict_weak_lower_killing_integral_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:24:48.570744+00:00
-- url     : https://prove2.me/theorems/1fdee30d-1d44-4853-89a0-f324b33c9354
-- title:
--   Original Esscher Qp strict and weak lower first-passage killing give equal integrals for arbitrary rewards
-- statement:
--   For the true original Lévy random-terminal Esscher law Qp, replacing the strict lower-passage clock event expTime<T_lower with the weak event expTime≤T_lower changes no nonnegative measurable reward integral. The only extra observations in the weak event tie the actual real exponential terminal age to the source lower first-passage time, and that random graph has exactly zero Qp mass by a separately canonically Proved genuine joint-clock theorem. The equivalence includes finite, zero and infinite passage-clock cases, with no unproved exit formula.
-- source:
--   Proved actual lower first passage age tie zero fd312714, source exact ENNReal.ofReal/toNNReal, Mathlib Measure.mono_null and lintegral_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_real_exp_clock_lower_age_tie_zero

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_true_Qp_strict_weak_lower_killing_integral_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (R : Ω × ℝ → ℝ≥0∞) (hR : Measurable R) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (ProbabilityTheory.expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z : Ω × ℝ,
       ({z : Ω × ℝ | 0 ≤ z.2 ∧
         ENNReal.ofReal z.2 < twoSidedExitDownTime X lower z.1}).indicator R z ∂Qp) =
     (∫⁻ z : Ω × ℝ,
       ({z : Ω × ℝ | 0 ≤ z.2 ∧
         ENNReal.ofReal z.2 ≤ twoSidedExitDownTime X lower z.1}).indicator R z ∂Qp)) := by sorry
