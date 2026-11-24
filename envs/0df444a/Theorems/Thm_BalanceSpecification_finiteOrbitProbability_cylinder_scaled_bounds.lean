-- Prove2me | Theorems.Thm_BalanceSpecification_finiteOrbitProbability_cylinder_scaled_bounds
-- name    : BalanceSpecification.finiteOrbitProbability_cylinder_scaled_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:58.77518+00:00
-- url     : https://prove2.me/theorems/1b68fc5e-3b82-4a99-a763-7caedbc949d1
-- title:
--   Balance Specification: finite Orbit Probability cylinder scaled bounds
-- statement:
--   Averaging only over the middle third keeps every fixed-length cylinder
--   strictly inside the realized words, eliminating boundary-cylinder errors.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L376-L438
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L376-L438

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

theorem BalanceSpecification.finiteOrbitProbability_cylinder_scaled_bounds (hX : X.carrier.Nonempty)
    {cL cR C : ℝ} (hcL : 0 ≤ cL) (hcR : 0 ≤ cR) (hC : 1 ≤ C)
    (hupper : ∀ n : ℕ, (wordCount (language X) n : ℝ) ≤
      C * Real.exp ((n : ℝ) * entropy X hX))
    (hR : ∀ u ∈ language X, ∀ n : ℕ, 1 ≤ n →
      cR * (wordCount (language X) n : ℝ) ≤ (followerFinset (language X) u n).card)
    (hP : ∀ u ∈ language X, ∀ n : ℕ, 1 ≤ n →
      cL * (wordCount (language X) n : ℝ) ≤ (predecessorFinset (language X) u n).card)
    (n : ℕ) [Nonempty ↥(wordFinset (language X) (3 * (n + 1)))]
    (x : ↥(wordFinset (language X) (3 * (n + 1))) → X.carrier)
    (hx : ∀ w, block (x w).val 0 (3 * (n + 1)) = w.val)
    {u : Word A} (hu : u ∈ language X) (hlen : u.length ≤ n + 1) :
    cL * cR / C ≤
        (finiteOrbitProbability (shiftMap X) (fun w => (shiftMap X)^[n + 1] (x w)) n :
          Measure X.carrier).real (cylinder X u 0) *
            Real.exp ((u.length : ℝ) * entropy X hX) ∧
    (finiteOrbitProbability (shiftMap X) (fun w => (shiftMap X)^[n + 1] (x w)) n :
          Measure X.carrier).real (cylinder X u 0) *
            Real.exp ((u.length : ℝ) * entropy X hX) ≤ C * C := by sorry
