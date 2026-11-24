-- Prove2me | Theorems.Thm_BalanceSpecification_word_eq_of_projection_maps
-- name    : BalanceSpecification.word_eq_of_projection_maps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:46:28.925624+00:00
-- url     : https://prove2.me/theorems/6ed9ed18-acd4-4651-855f-52302e863f7a
-- title:
--   Balance Specification: word eq of projection maps
-- statement:
--   The Balance Specification construction uses the word eq of projection maps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L43-L46
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L43-L46

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_ProductShift
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A B : Type*}

theorem BalanceSpecification.word_eq_of_projection_maps {u v : Word (A × B)}
    (h1 : u.map Prod.fst = v.map Prod.fst) (h2 : u.map Prod.snd = v.map Prod.snd) :
    u = v := by sorry
