-- Prove2me | Theorems.Thm_BalanceSpecification_translatedProbability_cylinder_real
-- name    : BalanceSpecification.translatedProbability_cylinder_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:12:26.221392+00:00
-- url     : https://prove2.me/theorems/3e6ee5fd-cc56-409d-a8ed-6c9b0052dc6f
-- title:
--   Balance Specification: translated Probability cylinder real
-- statement:
--   The Balance Specification construction uses the translated Probability cylinder real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L27-L35
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L27-L35

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_VariationalPrinciple
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.translatedProbability_cylinder_real (μ : ProbabilityMeasure X.carrier)
    (k : ℕ) (w : Word A) (l : ℤ) :
    (translatedProbability μ k : Measure X.carrier).real (cylinder X w l) =
      (μ : Measure X.carrier).real (cylinder X w ((k : ℤ) + l)) := by sorry
