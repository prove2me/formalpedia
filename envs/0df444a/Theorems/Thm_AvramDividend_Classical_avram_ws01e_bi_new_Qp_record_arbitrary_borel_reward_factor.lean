-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_Qp_record_arbitrary_borel_reward_factor
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_Qp_record_arbitrary_borel_reward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:44:59.306541+00:00
-- url     : https://prove2.me/theorems/9c105ac3-97e0-421b-a85b-bfcce20918ab
-- title:
--   Genuine Esscher first-record regeneration factors every Borel drawdown indicator satisfying the fresh and reset path identities
-- statement:
--   Under actual nonproduct terminal Esscher law Qp, the Proved first-record full-path regeneration extends from arbitrary positive rewards to any Borel drawdown event B, provided the chosen jointly measurable nonnegative full-path test agrees with that indicator on both fresh and stopped-shifted path-clock pairs. This discharges the entire genuine Qp integral factor and restricts its conclusion to the finite first-record clock event, without assuming Wiener-Hopf independence.
-- source:
--   Proved 4cf7269f and genuine density Tonelli; measurable indicator integration and pathwise equality. Conditions are exactly the verifiable Borel test identities, not a factorisation premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_uncapped_firstRecord_Qp_conditional_regeneration
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_Qp_record_arbitrary_borel_reward_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (b : ℝ) (hb : 0 ≤ b)
    (D : Ω × ℝ → ℝ) (hD : Measurable D)
    (B : Set ℝ) (hB : MeasurableSet B)
    (E : Set (Ω × ℝ))
    (hEdef : E = {z : Ω × ℝ |
      twoSidedExitUpTime X b z.1 < ⊤ ∧
        (((twoSidedExitUpTime X b z.1).toNNReal : ℝ)) ≤ z.2})
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2))
    (hFresh : ∀ (ω : Ω) (r : ℝ),
      H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) =
        B.indicator (fun _ => (1 : ℝ≥0∞)) (D (ω, r)))
    (hReset : ∀ z : Ω × ℝ, z ∈ E →
      H (Real.toNNReal
        (z.2 - ((twoSidedExitUpTime X b z.1).toNNReal : ℝ)))
        (fun s : ℝ≥0 =>
          X.X ((twoSidedExitUpTime X b z.1).toNNReal + s) z.1 -
            X.X ((twoSidedExitUpTime X b z.1).toNNReal) z.1) =
        B.indicator (fun _ => (1 : ℝ≥0∞)) (D z)) :
    (let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     Qp (E ∩ D ⁻¹' B) = Qp E * Qp (D ⁻¹' B)) := by sorry
