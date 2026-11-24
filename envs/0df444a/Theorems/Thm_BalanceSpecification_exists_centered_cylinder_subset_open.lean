-- Prove2me | Theorems.Thm_BalanceSpecification_exists_centered_cylinder_subset_open
-- name    : BalanceSpecification.exists_centered_cylinder_subset_open
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:12:22.10941+00:00
-- url     : https://prove2.me/theorems/1acbb693-bd09-403d-bd25-d6e87ab92ed6
-- title:
--   Balance Specification: exists centered cylinder subset open
-- statement:
--   The Balance Specification construction uses the exists centered cylinder subset open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TopologicalMixing.lean#L14-L50
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/TopologicalMixing.lean#L14-L50

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TopologicalMixing
set_option autoImplicit true
@[expose] public section
public section
open Set TopologicalSpace
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]

theorem BalanceSpecification.exists_centered_cylinder_subset_open {X : ShiftSpace A}
    {U : Set X.carrier} (hU : IsOpen U) {x : X.carrier} (hx : x ∈ U) :
    ∃ N : ℕ, ∃ w : Word A,
      w ∈ language X ∧ w.length = 2*N+1 ∧
      x ∈ cylinder X w (-(N : ℤ)) ∧ cylinder X w (-(N : ℤ)) ⊆ U := by sorry
