-- Prove2me | Theorems.Thm_Autoconvolutions_Blocks_mem_rows
-- name    : Autoconvolutions.Blocks.mem_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:10.805258+00:00
-- url     : https://prove2.me/theorems/51dad43d-43ae-4253-8d0c-fdc4e8c4b0bd
-- title:
--   Blocks: mem rows
-- statement:
--   The Blocks construction uses the mem rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockKeys.lean#L38-L42
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockKeys.lean#L38-L42

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

theorem Autoconvolutions.Blocks.mem_rows {m u v D : ℕ} {I J : Finset (Fin m)} {t : Row m} :
    t ∈ rows I J u v D ↔ t.1.1 ∈ I.piAntidiag u ∧
      t.1.2 ∈ J.piAntidiag v ∧ t.2 < D := by sorry
