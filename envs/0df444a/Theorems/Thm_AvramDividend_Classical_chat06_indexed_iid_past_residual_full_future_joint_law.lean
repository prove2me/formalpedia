-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_past_residual_full_future_joint_law
-- name    : AvramDividend.Classical.chat06_indexed_iid_past_residual_full_future_joint_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:14:54.364983+00:00
-- url     : https://prove2.me/theorems/a478e89c-48c0-4a4b-a4f9-1949f5fa679d
-- title:
--   Complete joint law for indexed exponential residual survival and all subsequent waits
-- statement:
--   At any fixed iid exponential waiting-time index, an arbitrary measurable event of the masked earlier waiting times, survival of the current wait beyond an arbitrary measurable nonnegative past age, and any measurable event of the entire subsequent infinite waiting suffix have an exact joint factorisation. Its factor is the past-current survival probability multiplied by e^(-t) and the common whole-suffix law. The proof combines three accepted results: prefix/current-wait versus suffix independence, past-event exponential residual memorylessness, and independent future-suffix probability factorisation. It prepares the complete future Poisson renewal law after random count selection; that selection is a subsequent obligation.
-- source:
--   Source bv_indexed_iid_past_residual_full_future_joint_law_chat06_20261021.lean, 77 lines, SHA-256 68f16ebc6c12888f904f5e099ebc0d5c14bfa5c099562140487a4451c8d63afb. Private probe 5d577ae5-be1c-4693-85d1-89b89d8da3ec passed to its sentinel with zero source errors at pinned Mathlib. Official acceptance remains separate.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_prefix_current_wait_future_independent
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_wait_prefix_random_age_residual
import Theorems.Thm_AvramDividend_Classical_chat06_past_residual_future_joint_factorisation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_indexed_iid_past_residual_full_future_joint_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ)
    (Z : Ω → (ℕ → ℝ))
    (hZ : Z = fun ω i => if h : i < n then τ i ω else 0)
    (age : (ℕ → ℝ) → ℝ) (hAge : Measurable age)
    (D B : Set (ℕ → ℝ)) (hD : MeasurableSet D)
    (hB : MeasurableSet B)
    (μ : Measure (ℕ → ℝ))
    (hLaw : HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (hNonneg : ∀ᵐ z ∂(P.map Z), 0 ≤ age z)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | (Z ω ∈ D ∧ age (Z ω) + t < τ n ω) ∧
      (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} =
      (P {ω | Z ω ∈ D ∧ age (Z ω) < τ n ω} *
        ENNReal.ofReal (Real.exp (-t))) * μ B := by sorry
