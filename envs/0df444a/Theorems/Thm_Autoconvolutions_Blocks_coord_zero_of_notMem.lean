-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_coord_zero_of_notMem
-- name    : Autoconvolutions.Blocks.coord_zero_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:28.491029+00:00
-- url     : https://prove2.me/theorems/03744426-a987-4698-9dae-23b3b23b40e7
-- title:
--   Blocks: coord zero of not Mem
-- statement:
--   The Blocks construction uses the coord zero of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockKeys.lean#L71-L74
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockKeys.lean#L71-L74

module
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_BlockKeys
set_option autoImplicit true
@[expose] public section
public section
open Autoconvolutions Autoconvolutions.Blocks
open Finset

theorem Autoconvolutions.Blocks.coord_zero_of_notMem {m k : ℕ} {I : Finset (Fin m)} {a : Fin m → ℕ}
    (ha : a ∈ I.piAntidiag k) {i : Fin m} (hi : i ∉ I) : a i = 0 := by sorry
