-- Prove2me | Theorems.Thm_BalanceSpecification_exists_near_pure_cylinder
-- name    : BalanceSpecification.exists_near_pure_cylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:15:00.428339+00:00
-- url     : https://prove2.me/theorems/3b71b6fe-89e3-46ee-a520-a1eead0690e6
-- title:
--   Balance Specification: exists near pure cylinder
-- statement:
--   Positive measurable sets have cylinders with conditional mass arbitrarily close to one.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsErgodic.lean#L95-L158
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsErgodic.lean#L95-L158

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

theorem BalanceSpecification.exists_near_pure_cylinder {X : ShiftSpace A}
    (μ : Measure X.carrier) [IsFiniteMeasure μ] {B : Set X.carrier}
    (hB : MeasurableSet B) (hBpos : 0 < μ.real B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w ∈ language X, ∃ k : ℤ,
      0 < μ.real (cylinder X w k) ∧
      (1 - δ) * μ.real (cylinder X w k) < μ.real (B ∩ cylinder X w k) := by sorry
