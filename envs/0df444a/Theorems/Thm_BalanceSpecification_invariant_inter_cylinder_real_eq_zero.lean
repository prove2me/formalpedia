-- Prove2me | Theorems.Thm_BalanceSpecification_invariant_inter_cylinder_real_eq_zero
-- name    : BalanceSpecification.invariant_inter_cylinder_real_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:44:30.43427+00:00
-- url     : https://prove2.me/theorems/3d1442b4-fc8d-4058-a7a8-31ef25185435
-- title:
--   Balance Specification: invariant inter cylinder real eq zero
-- statement:
--   The Balance Specification construction uses the invariant inter cylinder real eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsErgodic.lean#L14-L34
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsErgodic.lean#L14-L34

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [Fintype A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A]

theorem BalanceSpecification.invariant_inter_cylinder_real_eq_zero {X : ShiftSpace A}
    {μ : ProbabilityMeasure X.carrier} (hμ : IsInvariant μ)
    {B : Set X.carrier} (hB : MeasurableSet B)
    (hBinv : (shiftMap X) ⁻¹' B = B) (w : Word A) (k : ℤ) :
    (μ : Measure X.carrier).real (B ∩ cylinder X w k) =
      (μ : Measure X.carrier).real (B ∩ cylinder X w 0) := by sorry
