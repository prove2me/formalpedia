-- Prove2me | Theorems.Thm_BalanceSpecification_finitePointProbability_cylinder_real_of_length
-- name    : BalanceSpecification.finitePointProbability_cylinder_real_of_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:05.50321+00:00
-- url     : https://prove2.me/theorems/3459c89c-9a83-4c16-bf4a-4f65bf367ced
-- title:
--   Balance Specification: finite Point Probability cylinder real of length
-- statement:
--   The Balance Specification construction uses the finite Point Probability cylinder real of length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L288-L297
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L288-L297

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

theorem BalanceSpecification.finitePointProbability_cylinder_real_of_length
    {M : ℕ} (u : Word A) (a b : ℕ) (hM : M = a + u.length + b)
    [Nonempty ↥(wordFinset (language X) M)]
    (x : ↥(wordFinset (language X) M) → X.carrier)
    (hx : ∀ w, block (x w).val 0 M = w.val) :
    (finitePointProbability (fun w => (shiftMap X)^[a] (x w)) : Measure X.carrier).real
        (cylinder X u 0) =
      ((occurrenceFinset (language X) u a b).card : ℝ) / wordCount (language X) M := by sorry
