-- Prove2me | Theorems.Thm_BalanceSpecification_occurrence_ratio_scaled_bounds
-- name    : BalanceSpecification.occurrence_ratio_scaled_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:08:07.734805+00:00
-- url     : https://prove2.me/theorems/1e148b3b-4706-4c13-a1f6-a2f27f880e54
-- title:
--   Balance Specification: occurrence ratio scaled bounds
-- statement:
--   The two-sided counting bounds give uniform Gibbs-scale bounds whenever both
--   side lengths are positive. Every numerical input is supplied from balancedness
--   and the BSM word-count envelope in the existence theorem below.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L303-L372
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L303-L372

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology ENNReal Classical BoundedContinuousFunction
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
omit [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]

theorem BalanceSpecification.occurrence_ratio_scaled_bounds (hX : X.carrier.Nonempty)
    {cL cR C : ℝ} (hcL : 0 ≤ cL) (hcR : 0 ≤ cR) (hC : 1 ≤ C)
    (hupper : ∀ n : ℕ, (wordCount (language X) n : ℝ) ≤
      C * Real.exp ((n : ℝ) * entropy X hX))
    (hR : ∀ u ∈ language X, ∀ n : ℕ, 1 ≤ n →
      cR * (wordCount (language X) n : ℝ) ≤ (followerFinset (language X) u n).card)
    (hP : ∀ u ∈ language X, ∀ n : ℕ, 1 ≤ n →
      cL * (wordCount (language X) n : ℝ) ≤ (predecessorFinset (language X) u n).card)
    {u : Word A} (hu : u ∈ language X) {a b M : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hM : M = a + u.length + b) :
    cL * cR / C ≤ ((occurrenceFinset (language X) u a b).card : ℝ) /
        wordCount (language X) M * Real.exp ((u.length : ℝ) * entropy X hX) ∧
    ((occurrenceFinset (language X) u a b).card : ℝ) /
        wordCount (language X) M * Real.exp ((u.length : ℝ) * entropy X hX) ≤ C * C := by sorry
