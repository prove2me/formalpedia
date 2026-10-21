-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_finite_simple_state
-- name    : AvramDividend.Classical.levy_increment_condExp_finite_simple_state
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T16:29:18.356481+00:00
-- url     : https://prove2.me/theorems/0de453cb-633f-4cc1-9a60-4bca488e5859
-- title:
--   Finite sums of past-measurable simple-state Lévy payoffs commute with conditional transition expectations
-- statement:
--   For an arbitrary finite set of states i, each deterministic reserve x_i, and any events A_i∈F_s (disjointness not required), and a Borel real payoff f whose shifted stationary-increment payoff at each i is integrable, E[Σ 1_{A_i} f(x_i+X_t−X_s) | F_s] equals Σ 1_{A_i} E[f(x_i+X_(t−s))]. This is the finite simple-state version of the Markov conditional-expectation operator needed for approximating a bounded F_s-measurable reserve by simple random variables, while depending only on already Proved deterministic-capital past-event conditional expectation and exact remote-certified condExp_add/Integrable.indicator declarations. Use finite induction to assemble integrability and conditional-expectation equality. The result is valid even for overlapping past events by linearity, and does not assert continuity of the semigroup in the state or identify the general Lévy generator; those still require independent analytic proofs.
-- source:
--   Uses authoritative accepted levy_increment_condExp_Borel_on_past_event 7bbeae01-2433-48cd-8583-b64760ebbadd and pinned exact condExp_add and Integrable.indicator signatures.

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_Borel_on_past_event

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_increment_condExp_finite_simple_state
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (f : ℝ → ℝ) (hf : Measurable f)
    (A : ι → Set Ω)
    (hA : ∀ i ∈ S, MeasurableSet[𝓕 s] (A i))
    (hI : ∀ i ∈ S,
      Integrable (fun ω => f (x i + X.X (t - s) ω)) P) :
    P[(fun ω => ∑ i ∈ S,
      (A i).indicator
        (fun ω' => f (x i + (X.X t ω' - X.X s ω'))) ω) | 𝓕 s] =ᵐ[P]
      (fun ω => ∑ i ∈ S,
        (A i).indicator
          (fun _ => ∫ ω', f (x i + X.X (t - s) ω') ∂P) ω) := by sorry
