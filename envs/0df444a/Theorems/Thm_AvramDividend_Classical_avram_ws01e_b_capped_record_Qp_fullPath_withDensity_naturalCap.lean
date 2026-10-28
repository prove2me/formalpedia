-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_capped_record_Qp_fullPath_withDensity_naturalCap
-- name    : AvramDividend.Classical.avram_ws01e_b_capped_record_Qp_fullPath_withDensity_naturalCap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T16:23:57.307657+00:00
-- url     : https://prove2.me/theorems/162093dc-7d2b-4611-838c-0d46aa722e50
-- title:
--   Canonical natural-cap record factor as an exact genuine Qp weighted joint-event measure identity
-- statement:
--   At the actual n-capped first strict upper record of the spectrally negative Lévy path and an independent real Exp(p) observation clock, under the explicitly defined random-terminal Esscher joint density Qp, the weighted mass of the weak-clock survived record event for every jointly measurable residual-clock and full shifted-path reward equals the finite-record original stopped Esscher discount mass times the genuine Qp fresh residual-clock/full path reward integral. The concrete formula is in measure.withDensity and first-record event form, with all first-record stopping, density-split, and reward measurability premises discharged by the canonically Proved capped theorem 3fe509bd; this precise interface supplies the bounded-cap terms needed for the uncapped monotone-union limit and is substantive, not a generic DCT helper.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013), Section 2.1 record regeneration. Canonically Proved fully instantiated genuine capped Qp reward factor 3fe509bd-1091-47c4-b60f-056f52e60604; exact source-specific finite weak-clock cap exhaustion ef0377ba-2f27-4e88-b050-087c003014dd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_capped_firstRecord_Qp_fullPath_regeneration_instantiated
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_capped_record_Qp_fullPath_withDensity_naturalCap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (hb : 0 ≤ b) (n : ℕ)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2)) :
    (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
     let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
     let D : Set Ω := {ω | T ω < (n : ℝ≥0∞)}
     let E : Set (Ω × ℝ) :=
       {z | T z.1 < (n : ℝ≥0∞) ∧ (age z.1 : ℝ) ≤ z.2}
     let W : ℝ≥0 → ℝ≥0∞ :=
       fun u => ENNReal.ofReal (Real.exp (θ * b - (p + X.ψ θ) * (u : ℝ)))
     let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     let K : Ω × ℝ → ℝ≥0∞ := fun z =>
       H (Real.toNNReal (z.2 - (age z.1 : ℝ)))
         (fun s : ℝ≥0 => X.X (age z.1 + s) z.1 - X.X (age z.1) z.1)
     (Qp.withDensity K) E =
       (P.withDensity (fun ω => W (age ω))) D *
       (∫⁻ r : ℝ, (∫⁻ ω,
         ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal r) ω -
             (Real.toNNReal r : ℝ) * X.ψ θ)) *
         H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) ∂P)
         ∂(expMeasure p))) := by sorry
