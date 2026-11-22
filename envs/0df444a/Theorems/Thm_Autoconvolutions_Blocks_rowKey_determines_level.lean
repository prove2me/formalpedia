-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_rowKey_determines_level
-- name    : Autoconvolutions.Blocks.rowKey_determines_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:09.955252+00:00
-- url     : https://prove2.me/theorems/2f2f7dc7-47af-48d8-b162-8dd6ad68cd70
-- title:
--   Blocks: row Key determines level
-- statement:
--   After recovering a row, its right-digit sum determines the level.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockKeys.lean#L111-L121
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockKeys.lean#L111-L121

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

theorem Autoconvolutions.Blocks.rowKey_determines_level {m n s s' D : ℕ} {I J : Finset (Fin m)}
    (hD : 1 < D) (hd : Disjoint I J) (hs : s ≤ 2*n) (hs' : s' ≤ 2*n)
    (hnD : 4*n < D) {t t' : Row m}
    (ht : t ∈ rows I J (2*n-s) (2*n+s) D)
    (ht' : t' ∈ rows I J (2*n-s') (2*n+s') D)
    (he : rowKey D t = rowKey D t') : s = s' ∧ t = t' := by sorry
