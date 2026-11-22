-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_succ_succ
-- name    : DeciSigma1.Holes.Fresh.mem_active_succ_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:51.517708+00:00
-- url     : https://prove2.me/theorems/dcb8b694-bd22-4a73-aa52-2a1adb50dd40
-- title:
--   Fresh: mem active succ succ
-- statement:
--   A coordinate stays active iff it has an internal anchor.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L467-L475
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L467-L475

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
variable (W : Fin k → List α)

theorem DeciSigma1.Holes.Fresh.mem_active_succ_succ {t : ℕ} {l : Fin k} :
    l ∈ active W (t + 2) ↔
      l ∈ active W (t + 1) ∧ ∃ e ∈ anchors W (t + 1) l, e < (W l).length := by sorry
