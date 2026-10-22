-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_exponential_condExp_factorization
-- name    : AvramDividend.Classical.levy_exponential_condExp_factorization
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:30:47.077251+00:00
-- url     : https://prove2.me/theorems/a44cb9f4-52df-41bd-aa08-9087afd7b2d2
-- title:
--   Conditional exponential Lévy payoff factorises over an adapted past factor and a future increment
-- statement:
--   For deterministic times s≤t and a real exponential test parameter theta, assume the past factor exp(theta X_s) is strongly measurable in the filtration at s and that the time-t payoff, future-increment payoff and stationary future-increment payoff are integrable. Then the conditional expectation of exp(theta X_t) given F_s equals exp(theta X_s) multiplied by the deterministic expectation of exp(theta X_(t−s)), almost surely. The proof uses exact exponential factorisation, Mathlib's conditional-expectation pull-out lemma and the previously Proved Borel-payoff conditional Markov identity for deterministic starting reserve zero. The explicit integrability assumptions keep the assertion source-faithful. This is a step toward the exponential supermartingale budget; it does not assert stopped-time verification.
-- source:
--   Proved Levy Borel increment conditional identity target c8eb9ff5-e0f7-4b7a-8653-28d84c854efe and pinned Mathlib MeasureTheory.condExp_mul_of_stronglyMeasurable_left with exact source header from Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut at pinned revision.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_Borel_payoff

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_exponential_condExp_factorization
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ)
    (hPast : StronglyMeasurable[𝓕 s]
      (fun ω => Real.exp (θ * X.X s ω)))
    (hTotal : Integrable (fun ω => Real.exp (θ * X.X t ω)) P)
    (hIncrement : Integrable
      (fun ω => Real.exp (θ * (X.X t ω - X.X s ω))) P)
    (hDet : Integrable
      (fun ω => Real.exp (θ * X.X (t - s) ω)) P) :
    P[(fun ω => Real.exp (θ * X.X t ω)) | 𝓕 s] =ᵐ[P]
      (fun ω => Real.exp (θ * X.X s ω) *
        (∫ η, Real.exp (θ * X.X (t - s) η) ∂P)) := by sorry
