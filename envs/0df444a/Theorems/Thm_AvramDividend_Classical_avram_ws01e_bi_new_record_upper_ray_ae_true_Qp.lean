-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_record_upper_ray_ae_true_Qp
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_record_upper_ray_ae_true_Qp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:51:53.76751+00:00
-- url     : https://prove2.me/theorems/4615283e-ae2b-47c9-b992-c1beca095348
-- title:
--   Strict Esscher random-terminal upper-ray event agrees almost surely with the censored genuine first-record clock event
-- statement:
--   For a genuine spectrally negative Lévy process under the actual random-terminal Esscher density, every nonnegative strict supremum threshold event S_e>b agrees Qp-almost surely with the finite first-record event T_b<infinity and T_b<=e. The pathwise strict equivalence uses the accepted upcrossing theorem; the only possible discrepancy is equality of the independent atomless real exponential clock with the stopping age, still null after withDensity.
-- source:
--   Derived from accepted b626324c strict upcrossing equivalence and absolute continuity of genuine Qp with respect to P product expMeasure p; essential source-faithful event bridge for all Borel Wiener–Hopf factorisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_record_upper_ray_ae_true_Qp
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (b : ℝ) (hb : 0 ≤ b) :
    (let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
     let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
     ({z : Ω × ℝ | b < runningSup X (Real.toNNReal z.2) z.1}) =ᵐ[Qp]
       {z : Ω × ℝ | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}) := by sorry
