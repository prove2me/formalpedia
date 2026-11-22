-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_rowKey_injective
-- name    : Autoconvolutions.Blocks.rowKey_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:11.016869+00:00
-- url     : https://prove2.me/theorems/48650032-147f-44bf-a939-0ffe30fa6969
-- title:
--   Blocks: row Key injective
-- statement:
--   Across arbitrary levels, bounded totals and disjoint supports make the
--   low digit and the two multiplicity vectors individually recoverable.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockKeys.lean#L86-L108
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockKeys.lean#L86-L108

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

theorem Autoconvolutions.Blocks.rowKey_injective {m u v u' v' D : ℕ} {I J : Finset (Fin m)}
    (hD : 1 < D) (hd : Disjoint I J) (huv : u+v < D) (huv' : u'+v' < D)
    {t t' : Row m} (ht : t ∈ rows I J u v D) (ht' : t' ∈ rows I J u' v' D)
    (he : rowKey D t = rowKey D t') : t = t' := by sorry
