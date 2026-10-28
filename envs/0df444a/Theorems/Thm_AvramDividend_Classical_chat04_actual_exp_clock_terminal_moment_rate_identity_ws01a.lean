-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_actual_exp_clock_terminal_moment_rate_identity_ws01a
-- name    : AvramDividend.Classical.chat04_actual_exp_clock_terminal_moment_rate_identity_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T10:16:27.695055+00:00
-- url     : https://prove2.me/theorems/3281a368-4194-4593-baf1-48bda44397f6
-- title:
--   Exact positive exponential-clock Lévy terminal moment at a rate gap
-- statement:
--   For the actual Lévy path law and independent exponential time of rate r>0, and any positive Laplace tilt parameter θ≥0 with ψ(θ)<r, the genuine exponential terminal moment satisfies (r-ψ(θ))E[exp(θ(x+X_e))]=r exp(θx), expressed in ENNReal so no unstated integrability hypothesis is required. The positive rate gap forces the moment finite. This is the missing independent exponential-clock integrability input for the genuine lower-killed q-scale reward via the separately published 1A exponential domination theorem, not a Wiener–Hopf factor assumption.
-- source:
--   Canonical 1A actual exponential-clock semigroup eigenfunction action 728dab06 (Proved, candidate 17520) and pinned exponentialPDF exact formula plus expMeasure probability mass. An exact density-rate tilt calculation, no killed spatial resolvent or two-sided exit identity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exp_clock_exponential_eigenfunction_action_ws01a

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_actual_exp_clock_terminal_moment_rate_identity_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r)
    (θ : ℝ) (hθ : 0 ≤ θ) (hgap : X.ψ θ < r) (x : ℝ) :
    ENNReal.ofReal (r - X.ψ θ) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp
          (θ * (x + X.X (Real.toNNReal z.2) z.1)))
        ∂(P.prod (ProbabilityTheory.expMeasure r))) =
    ENNReal.ofReal r * ENNReal.ofReal (Real.exp (θ * x)) := by sorry
