-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_low_and_high
-- name    : Autoconvolutions.Blocks.low_and_high
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:06.62742+00:00
-- url     : https://prove2.me/theorems/14c91665-3126-48f0-a8d2-e97849926eef
-- title:
--   Blocks: low and high
-- statement:
--   The Blocks construction uses the low and high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockKeys.lean#L61-L69
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockKeys.lean#L61-L69

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

theorem Autoconvolutions.Blocks.low_and_high {m D h h' : ℕ} (hD : 1 < D) {a b : Fin m → ℕ}
    (ha : ∀ i, a i < D) (hb : ∀ i, b i < D) (hh : h < D) (hh' : h' < D)
    (heq : h + D*code D a = h' + D*code D b) : h = h' ∧ a = b := by sorry
