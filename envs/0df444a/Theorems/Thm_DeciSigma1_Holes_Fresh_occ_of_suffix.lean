-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_occ_of_suffix
-- name    : DeciSigma1.Holes.Fresh.occ_of_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:30.356806+00:00
-- url     : https://prove2.me/theorems/16ddbd7c-a261-43d7-ae19-d6113f70637f
-- title:
--   Fresh: occ of suffix
-- statement:
--   A suffix `u` of a word is the drop at `|w| - |u|`, hence occurs there.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L123-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L123-L124

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
variable {x u v : List α}

theorem DeciSigma1.Holes.Fresh.occ_of_suffix {w : List α} (hu : u <:+ w) : u <+: w.drop (w.length - u.length) := by sorry
