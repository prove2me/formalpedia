-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_Borel_on_past_event
-- name    : AvramDividend.Classical.levy_increment_condExp_Borel_on_past_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:06:22.303028+00:00
-- url     : https://prove2.me/theorems/7bbeae01-2433-48cd-8583-b64760ebbadd
-- title:
--   Conditional expectation of a shifted Lévy payoff restricted to a measurable past event
-- statement:
--   Let X be the existing Lévy process, s≤t, f any measurable real payoff, x a deterministic reserve shift, and A any event measurable at F_s. If f(x+X_(t−s)) is integrable, the conditional expectation of 1_A f(x+X_t−X_s) given F_s equals 1_A times its stationary unconditional expectation. Apply the Proved generic deterministic-state increment conditional expectation, stationarity to transfer integrability, and the pinned condExp_indicator lemma for A∈F_s. This supports killed semigroup constructions, where A is the event of having survived before s. It is not the survival-to-t event and does not identify path crossing or the generator drift; those remain unproved.
-- source:
--   Dependency-gated on target levy_increment_condExp_Borel_payoff after authoritative Proved. Uses the exact accepted Chat04 event-conditioning proof pattern and Mathlib condExp_indicator.

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_Borel_payoff

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_increment_condExp_Borel_on_past_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (x : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (hInt : Integrable (fun ω => f (x + X.X (t - s) ω)) P) :
    P[A.indicator (fun ω => f (x + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      A.indicator (fun _ => ∫ ω, f (x + X.X (t - s) ω) ∂P) := by sorry
