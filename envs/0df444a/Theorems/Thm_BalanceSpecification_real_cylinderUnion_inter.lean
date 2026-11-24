-- Prove2me | Theorems.Thm_BalanceSpecification_real_cylinderUnion_inter
-- name    : BalanceSpecification.real_cylinderUnion_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:14:55.44089+00:00
-- url     : https://prove2.me/theorems/3c6cf6fd-bb16-481e-b52d-0d5d88e617cb
-- title:
--   Balance Specification: real cylinder Union inter
-- statement:
--   Finite equal-length cylinder partitions remain disjoint after restriction.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsErgodic.lean#L37-L50
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsErgodic.lean#L37-L50

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

theorem BalanceSpecification.real_cylinderUnion_inter {X : ShiftSpace A} (μ : Measure X.carrier)
    [IsFiniteMeasure μ] (S : Finset (Word A)) (l : ℕ)
    (hlen : ∀ a ∈ S, a.length = l) (k : ℤ) (C : Set X.carrier)
    (hC : MeasurableSet C) :
    μ.real ((⋃ a ∈ S, cylinder X a k) ∩ C) =
      ∑ a ∈ S, μ.real (cylinder X a k ∩ C) := by sorry
