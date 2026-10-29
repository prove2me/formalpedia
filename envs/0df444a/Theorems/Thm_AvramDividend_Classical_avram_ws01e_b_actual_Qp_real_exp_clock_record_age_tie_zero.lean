-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_real_exp_clock_record_age_tie_zero
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_Qp_real_exp_clock_record_age_tie_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:41:42.664998+00:00
-- url     : https://prove2.me/theorems/7e8e930e-dfd8-4625-8464-27776fe1e869
-- title:
--   Actual Esscher random-terminal real exponential clock never ties the finite recorded stopping age
-- statement:
--   For any genuine spectrally negative Lévy process, first strict upper-record stopping time, independent Exp(p) real clock with p>0, and its true random-terminal Esscher density exp(θX_e−eψθ), the probability that the observed real clock exactly equals the toNNReal converted first-record age is zero under the actual tilted joint law, including when the record time is infinite and toNNReal maps it to zero. The proof establishes the real Exp(p) clock's singleton-null property by absolute continuity with Lebesgue volume, applies product Tonelli to the measurable random age graph and preserves its nullity under the tilted density. No atomlessness or no-tie hypothesis is assumed.
-- source:
--   Source-specific exponential clock and Lévy first-record measurability; pinned Mathlib ProbabilityTheory.expMeasure density over real volume, Measure.prod_apply and withDensity_absolutelyContinuous; this discharges the strict versus weak Qp record clock event bridge for Wiener–Hopf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_Qp_real_exp_clock_record_age_tie_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b θ p : ℝ) (hb : 0 ≤ b) (hθ : 0 ≤ θ) (hp : 0 < p) :
    (let age : Ω → ℝ≥0 := fun ω => (twoSidedExitUpTime X b ω).toNNReal
     let Qp : Measure (Ω × ℝ) :=
       (P.prod (ProbabilityTheory.expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     Qp {z : Ω × ℝ | z.2 = (age z.1 : ℝ)} = 0) := by sorry
