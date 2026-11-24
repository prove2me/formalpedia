-- Prove2me | Theorems.Thm_BalanceSpecification_exists_injective_centered_block
-- name    : BalanceSpecification.exists_injective_centered_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:07.569841+00:00
-- url     : https://prove2.me/theorems/c80ec740-69fd-43c6-9c4e-1ebfeebf33f4
-- title:
--   Balance Specification: exists injective centered block
-- statement:
--   A finite collection of distinct configurations is distinguished by one
--   common centered block.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L23-L58
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Periodicity.lean#L23-L58

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}

theorem BalanceSpecification.exists_injective_centered_block (s : Finset (Configuration A)) :
    ∃ M : ℕ, Set.InjOn (fun x => block x (-(M : ℤ)) (2 * M + 1)) (s : Set (Configuration A)) := by sorry
