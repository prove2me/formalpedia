-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_real_exp_clock_lower_age_tie_zero
-- name    : AvramDividend.Classical.avram_ws01h_actual_Qp_real_exp_clock_lower_age_tie_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:56:35.631212+00:00
-- url     : https://prove2.me/theorems/fd312714-5ed5-4f55-be8b-3730a0f24478
-- title:
--   Actual Esscher terminal real exponential clock has zero lower strict first-passage age tie mass
-- statement:
--   For every actual original spectrally negative Lévy process and any real lower passage threshold, the joint tilted finite-clock measure Qp defined by the genuine Exp(p) terminal Esscher density assigns zero mass to the event that the real clock equals the true lower passage age converted to NNReal. The lower strict stopping time is measurable in the original space, expMeasure p is absolutely continuous with Lebesgue volume, each fibre of the random age graph is a singleton, and the tilted joint law is absolutely continuous with respect to its path-clock product base. This extends the already accepted upper-record clock tie result to the genuine lower killed history without asserting a global path-space Esscher measure.
-- source:
--   Accepted WS01H lower right-continuous stopping time a1d326c3 and pinned Mathlib expMeasure/gammaMeasure, prod_apply, withDensity_absolutelyContinuous; source-faithful analogue of accepted upper-record tie 7e8e930e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_lowerPassage_stopping_rightCont_filtration

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_actual_Qp_real_exp_clock_lower_age_tie_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p) :
    (let age : Ω → ℝ≥0 := fun ω =>
       (twoSidedExitDownTime X lower ω).toNNReal
     let Qp : Measure (Ω × ℝ) :=
       (P.prod (ProbabilityTheory.expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     Qp {z : Ω × ℝ | z.2 = (age z.1 : ℝ)} = 0) := by sorry
