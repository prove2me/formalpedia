-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_fixed_count_prefix_event_residual_future_joint
-- name    : AvramDividend.Classical.chat06_fixed_count_prefix_event_residual_future_joint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:37:07.162921+00:00
-- url     : https://prove2.me/theorems/334a02aa-a195-4e6c-97e1-fd962cc777de
-- title:
--   Fixed-clock residual and whole-future suffix independent of arbitrary measurable earlier waiting-time prefix events on a count cylinder
-- statement:
--   For a fixed renewal count n at an observation clock, consider any measurable event Q of the entire truncated prefix of waiting times before the current wait. If the count event N=n agrees almost surely with the corresponding arrival interval, the iid waits have Exp(1) tails and the complete post-next-arrival suffix has law mu, then P(Q of prefix, N=n, residual>t, whole future in B) factors as P(Q of prefix,N=n)*exp(-t)*mu(B). The proof applies the accepted full-future fixed-prefix exponential joint theorem with the prefix event Q intersected with the arrival-age condition, then translates this event to the exact count cylinder by pathwise arrival-time algebra and almost-sure measure congruence. This directly establishes independence against arbitrary measurable earlier-waiting-time prefix events on each count cylinder, a step towards full Poisson natural-filtration independence.
-- source:
--   Source bv_fixed_count_prefix_event_residual_future_joint_v2_chat06_20261021.lean, 144 lines, 6294 bytes, SHA-256 22eb6b6b5bdff166ca6966bb108e91882bf11e91fc707227ab1fc3991f1986fc. Private probe 64d9dc61-e055-4321-8a4f-517bef326a65 passed remote source elaboration to deliberate sentinel with zero candidate errors. First version failed at a conjunction-associativity mismatch in change; fixed with explicit grouping.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_past_residual_full_future_joint_law

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_fixed_count_prefix_event_residual_future_joint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ)
    (Z : Ω → (ℕ → ℝ))
    (hZ : Z = fun ω i => if h : i < n then τ i ω else 0)
    (N : Ω → ℕ) (clock t : ℝ) (ht : 0 ≤ t)
    (Q : Set (ℕ → ℝ)) (hQ : MeasurableSet Q)
    (μ : Measure (ℕ → ℝ))
    (hLaw : HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (hCount :
      (fun ω : Ω => N ω = n) =ᵐ[P]
        (fun ω => (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock < ∑ i ∈ Finset.range (n + 1), τ i ω)) :
    P {ω | Z ω ∈ Q ∧ N ω = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω) ∧
      (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} =
      (P {ω | Z ω ∈ Q ∧ N ω = n} *
        ENNReal.ofReal (Real.exp (-t))) * μ B := by sorry
