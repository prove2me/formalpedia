-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_marker_ne_nil
-- name    : DeciSigma1.Holes.Fresh.marker_ne_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:07.502704+00:00
-- url     : https://prove2.me/theorems/2cfe9c97-0224-429c-997c-a77f81e0739d
-- title:
--   Fresh: marker ne nil
-- statement:
--   The Fresh construction uses the marker ne nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L507-L510
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L507-L510

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

theorem DeciSigma1.Holes.Fresh.marker_ne_nil {t : ℕ} (ht : 1 ≤ t) {m : Fin k}
    (hm : m ∈ active W t) : marker W t m ≠ [] := by sorry
