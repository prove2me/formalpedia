-- Prove2me | Theorems.Thm_BalanceSpecification_finitePointProbability_cylinder_real
-- name    : BalanceSpecification.finitePointProbability_cylinder_real
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:07:41.972032+00:00
-- url     : https://prove2.me/theorems/32a0e254-e5ea-4ea3-8173-2da8c51b490e
-- title:
--   Balance Specification: finite Point Probability cylinder real
-- statement:
--   The uniform realized-word measure has exactly the fixed-middle occurrence
--   ratio on any cylinder contained in the realized word.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L252-L286
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L252-L286

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

theorem BalanceSpecification.finitePointProbability_cylinder_real
    (u : Word A) (a b : ℕ)
    [Nonempty ↥(wordFinset (language X) (a + u.length + b))]
    (x : ↥(wordFinset (language X) (a + u.length + b)) → X.carrier)
    (hx : ∀ w, block (x w).val 0 (a + u.length + b) = w.val) :
    (finitePointProbability (fun w => (shiftMap X)^[a] (x w)) : Measure X.carrier).real
        (cylinder X u 0) =
      ((occurrenceFinset (language X) u a b).card : ℝ) /
        wordCount (language X) (a + u.length + b) := by sorry
