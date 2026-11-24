-- Prove2me | Theorems.Thm_BalanceSpecification_sum_follower_cylinder
-- name    : BalanceSpecification.sum_follower_cylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:11:51.793839+00:00
-- url     : https://prove2.me/theorems/da7e4799-45c6-4953-9215-fc73ec6d6660
-- title:
--   Balance Specification: sum follower cylinder
-- statement:
--   Right extensions partition the prefix cylinder after forbidden extensions
--   are removed; those removed cylinders have zero probability.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsBalance.lean#L79-L93
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsBalance.lean#L79-L93

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

theorem BalanceSpecification.sum_follower_cylinder (μ : ProbabilityMeasure X.carrier) (u : Word A) (n : ℕ) :
    (∑ w ∈ followerFinset (language X) u n,
      (μ : Measure X.carrier).real (cylinder X (u ++ w) 0)) =
        (μ : Measure X.carrier).real (cylinder X u 0) := by sorry
