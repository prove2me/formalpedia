-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_coord_le
-- name    : Autoconvolutions.Blocks.coord_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:12.736633+00:00
-- url     : https://prove2.me/theorems/24baeeef-1ebc-4110-bd46-c4fe5222b483
-- title:
--   Blocks: coord le
-- statement:
--   The Blocks construction uses the coord le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockKeys.lean#L76-L82
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockKeys.lean#L76-L82

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

theorem Autoconvolutions.Blocks.coord_le {m k : ℕ} {I : Finset (Fin m)} {a : Fin m → ℕ}
    (ha : a ∈ I.piAntidiag k) (i : Fin m) : a i ≤ k := by sorry
