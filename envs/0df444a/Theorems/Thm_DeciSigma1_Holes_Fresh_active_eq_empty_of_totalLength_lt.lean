-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_active_eq_empty_of_totalLength_lt
-- name    : DeciSigma1.Holes.Fresh.active_eq_empty_of_totalLength_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:34.780551+00:00
-- url     : https://prove2.me/theorems/d317f4ca-61c9-4c61-80d4-43cdda1da424
-- title:
--   Fresh: active eq empty of total Length lt
-- statement:
--   The Fresh construction uses the active eq empty of total Length lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L543-L550
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L543-L550

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
variable {W : Fin k → List α}

theorem DeciSigma1.Holes.Fresh.active_eq_empty_of_totalLength_lt {t : ℕ} (h : totalLength W < t) :
    active W t = ∅ := by sorry
