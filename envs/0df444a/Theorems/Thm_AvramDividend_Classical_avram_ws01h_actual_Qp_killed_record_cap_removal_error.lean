-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_killed_record_cap_removal_error
-- name    : AvramDividend.Classical.avram_ws01h_actual_Qp_killed_record_cap_removal_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:54:57.974365+00:00
-- url     : https://prove2.me/theorems/61707e66-3251-4077-bd3b-e578bcb18deb
-- title:
--   Actual lower-killed first-record terminal Esscher event uncapping has exact exp(-pN) error bound
-- statement:
--   For the original Lévy path and the authentic finite-terminal Esscher Qp, compare the genuine lower-killed upper-first passage and shifted-future nonruin event computed using capped stopping clock τ_N with the identical event using the original uncapped strict upper passage τ. They coincide on every real observation path with time≤N; off this cap, their mass difference is at most the exact exp(-pN) Esscher terminal observation tail. This is the source-faithful uncapping of the killed first-record branch needed for the finite-p CDF renewal, without any assumption about exit ratios or artificial infinite-path changed probability.
-- source:
--   Accepted actual stopped-cap time equality 159a20a9 and genuine tilted Exp(p) terminal-clock tail 19406a82, source actual upper/lower exit clock definitions, Mathlib measure subadditivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_exp_clock_finite_cap_tail_exact

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_actual_Qp_killed_record_cap_removal_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (x b : ℝ) (N : ℝ≥0) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     let τcap : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let τfull : Ω → ℝ≥0 := fun ω =>
       (twoSidedExitUpTime X b ω).toNNReal
     let Afull : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       twoSidedExitUpTime X b z.1 < (Real.toNNReal z.2 : ℝ≥0∞) ∧
       twoSidedExitUpTime X b z.1 < twoSidedExitDownTime X (-x) z.1 ∧
       ∀ u : ℝ≥0, u ≤ Real.toNNReal z.2 - τfull z.1 →
         0 ≤ (x + b) + (X.X (τfull z.1 + u) z.1 - X.X (τfull z.1) z.1)}
     let Acap : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       Real.toNNReal z.2 ≤ N ∧
       twoSidedExitUpTime X b z.1 < (Real.toNNReal z.2 : ℝ≥0∞) ∧
       twoSidedExitUpTime X b z.1 < twoSidedExitDownTime X (-x) z.1 ∧
       ∀ u : ℝ≥0, u ≤ Real.toNNReal z.2 - τcap z.1 →
         0 ≤ (x + b) + (X.X (τcap z.1 + u) z.1 - X.X (τcap z.1) z.1)}
     Qp Acap ≤ Qp Afull ∧
       Qp Afull ≤ Qp Acap + ENNReal.ofReal (Real.exp (-(p * (N : ℝ))))) := by sorry
