-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_ne_nil_of_mem_active
-- name    : DeciSigma1.Holes.Fresh.ne_nil_of_mem_active
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:30.937467+00:00
-- url     : https://prove2.me/theorems/a877e1c1-180d-4a1a-bef7-73a5ede0c58c
-- title:
--   Fresh: ne nil of mem active
-- statement:
--   The word of an active coordinate is nonempty.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L463-L464
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L463-L464

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

theorem DeciSigma1.Holes.Fresh.ne_nil_of_mem_active {t : ℕ} {l : Fin k} (hl : l ∈ active W t) : W l ≠ [] := by sorry
