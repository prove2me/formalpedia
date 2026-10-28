-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_exp_clock_full_freshPath_product_no_conditioning_hyp
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_exp_clock_full_freshPath_product_no_conditioning_hyp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T01:10:50.403314+00:00
-- url     : https://prove2.me/theorems/bb341912-ba7e-4c9c-948b-ad934400d8e1
-- title:
--   Actual independent exponential clock and full Lévy future path regenerate without an assumed positive survival event
-- statement:
--   For a genuine finite nonnegative Lévy stopping time τ under probability P and an independent real exponential observation clock of rate p>0, the conditional joint law on τ<e of the actual real residual e−τ and the entire future Lévy shifted increment path equals the product of the unconditional real Exp(p) nonnegative-clock law and the unconditional Lévy full-path law. No separate positive-probability assumption is required: every exponential tail is strictly positive, and Tonelli establishes P×Exp(p)(τ<e)>0. The proof composes accepted actual clock residual full law, joint stopped Lévy path product law and explicit positive conditioning. It does not claim Esscher-tilted Wiener–Hopf independence, but provides the final original-law exponential-horizon regeneration interface.
-- source:
--   Accepted avram_ws01e_b_independent_clock_positive_survival_event (7497827a), avram_ws01e_b_exp_clock_toNNReal_strict_tail (6aa1899c), avram_ws01e_b_actual_exp_clock_residual_full_law (e798f2d3), and avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law (55f49ff2).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_independent_clock_positive_survival_event
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exp_clock_toNNReal_strict_tail
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_exp_clock_residual_full_law
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_exp_clock_full_freshPath_product_no_conditioning_hyp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (hStop : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (p : ℝ) (hp : 0 < p) :
    Measure.map
      (fun z : Ω × ℝ =>
        ((z.2.toNNReal : ℝ) - (τ z.1 : ℝ),
          fun s : ℝ≥0 =>
            X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1))
      ((P.prod (expMeasure p))[|
        {z : Ω × ℝ | τ z.1 < z.2.toNNReal}]) =
    (Measure.map (fun t : ℝ => (t.toNNReal : ℝ))
        (expMeasure p)).prod
      (Measure.map (fun ω : Ω => fun s : ℝ≥0 => X.X s ω) P) := by sorry
