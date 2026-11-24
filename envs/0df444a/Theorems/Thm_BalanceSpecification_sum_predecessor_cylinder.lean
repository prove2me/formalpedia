-- Prove2me | Theorems.Thm_BalanceSpecification_sum_predecessor_cylinder
-- name    : BalanceSpecification.sum_predecessor_cylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:12:02.718741+00:00
-- url     : https://prove2.me/theorems/51103390-ef50-458d-a228-dd7aac2b40e2
-- title:
--   Balance Specification: sum predecessor cylinder
-- statement:
--   The analogous predecessor partition uses invariance to move its suffix
--   cylinder back to the origin.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsBalance.lean#L97-L114
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsBalance.lean#L97-L114

module
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsBalance
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.sum_predecessor_cylinder {μ : ProbabilityMeasure X.carrier} (hInv : IsInvariant μ)
    (u : Word A) (n : ℕ) :
    (∑ w ∈ predecessorFinset (language X) u n,
      (μ : Measure X.carrier).real (cylinder X (w ++ u) 0)) =
        (μ : Measure X.carrier).real (cylinder X u 0) := by sorry
