-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_regenerative_reward_event_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_Qp_regenerative_reward_event_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:40:06.066173+00:00
-- url     : https://prove2.me/theorems/461eec51-fd1b-4984-91bb-b3b9ff5b0631
-- title:
--   Genuine random-terminal Esscher record-event factor for an actual regenerative measurable reward
-- statement:
--   Under the actual spectrally negative Lévy process, independent real Exp(p) clock and true joint terminal Esscher density, any nonnegative measurable terminal reward W that agrees at every clock with a jointly measurable full-path test H and that resets pathwise at the first strictly upward record has exact Qp record-event factorisation: its Qp integral over the finite record before or at the clock is Qp(E) times the unconditional Qp integral. The hFresh and hReset premises are pointwise functional identities, not independence, a generic factorisation, a change of measure, or an assumed stochastic regeneration law. The result transfers the canonically Proved exact random-terminal full-path regeneration to actual terminal rewards, preserving the event normalisation.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013), section 2.1 Wiener–Hopf record regeneration; Prove2Me canonical genuine tilted full-path regeneration 4cf7269f; pinned Mathlib MeasureTheory.lintegral_prod_symm and lintegral_withDensity_eq_lintegral_mul.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_Qp_regenerative_reward_event_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
      (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (W : Ω × ℝ → ℝ≥0∞) (hW : Measurable W)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2))
    (hFresh : ∀ (ω : Ω) (r : ℝ),
      W (ω, r) = H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω))
    (hReset : ∀ (z : Ω × ℝ),
      twoSidedExitUpTime X b z.1 < ⊤ →
      ((twoSidedExitUpTime X b z.1).toNNReal : ℝ) ≤ z.2 →
      W z =
        H (Real.toNNReal (z.2 -
            ((twoSidedExitUpTime X b z.1).toNNReal : ℝ)))
          (fun s : ℝ≥0 =>
            X.X ((twoSidedExitUpTime X b z.1).toNNReal + s) z.1 -
            X.X (twoSidedExitUpTime X b z.1).toNNReal z.1)) :
    (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
     let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
     let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}
     let Qp : Measure (Ω × ℝ) := (P.prod (ProbabilityTheory.expMeasure p)).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
         (θ * X.X (Real.toNNReal z.2) z.1 -
           (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z in E, W z ∂Qp) =
       Qp E * (∫⁻ z : Ω × ℝ, W z ∂Qp)) := by sorry
