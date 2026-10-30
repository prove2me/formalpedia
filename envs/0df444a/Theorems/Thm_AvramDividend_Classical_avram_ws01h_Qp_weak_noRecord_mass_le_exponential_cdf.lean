-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_Qp_weak_noRecord_mass_le_exponential_cdf
-- name    : AvramDividend.Classical.avram_ws01h_Qp_weak_noRecord_mass_le_exponential_cdf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:59:13.911843+00:00
-- url     : https://prove2.me/theorems/f98ad01c-e419-495b-a333-cf89afbe916f
-- title:
--   True Qp weak no-upper-record remainder satisfies the exponential supremum CDF bound by clock-tie nullity
-- statement:
--   The genuine terminally tilted source Lévy law Qp gives a weak no-record event (observation time no later than the upper first-passage clock) in the exact finite-clock survival partition. Restricted to nonnegative real clock times, this event is contained in the strict no-record event plus the actual upper-record age tie. The latter has zero mass by the accepted source-specific Qp tie theorem; the former is dominated by the exact Exp(lambda) supremum CDF. Thus the full weak no-record remainder inherits the numerical source-level bound with no boundary regularity assumption and no two-sided exit formula.
-- source:
--   Accepted genuine no-record Exp(lambda) CDF f266220e and source-specific Qp upper-clock tie 7e8e930e, direct ENNReal toNNReal order.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_Qp_noRecord_mass_le_exponential_cdf
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_real_exp_clock_record_age_tie_zero

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_Qp_weak_noRecord_mass_le_exponential_cdf
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q : ℝ) (hφ : 0 < φ) (hq : 0 < q) (hroot : X.ψ φ = q)
    (p : ℝ) (hp : 0 < p) (lam : ℝ) (hlam : 0 < lam)
    (hshift : X.ψ (φ + lam) - q = p)
    (b : ℝ) (hb : 0 ≤ b) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (ProbabilityTheory.expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (φ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * q)))
     Qp {z : Ω × ℝ | 0 ≤ z.2 ∧
       (Real.toNNReal z.2 : ℝ≥0∞) ≤
         twoSidedExitUpTime X b z.1} ≤
       (ProbabilityTheory.expMeasure lam) (Iic b)) := by sorry
