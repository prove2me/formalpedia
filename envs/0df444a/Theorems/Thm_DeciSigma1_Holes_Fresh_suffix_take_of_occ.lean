-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_take_of_occ
-- name    : DeciSigma1.Holes.Fresh.suffix_take_of_occ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:28.561809+00:00
-- url     : https://prove2.me/theorems/cbcea984-7294-40d6-813d-2027a4aca4f5
-- title:
--   Fresh: suffix take of occ
-- statement:
--   A word that occurs at position `i` ends at the cut `i + |u|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L107-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L107-L108

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

theorem DeciSigma1.Holes.Fresh.suffix_take_of_occ {i : ℕ} (hu : u <+: x.drop i) : u <:+ x.take (i + u.length) := by sorry
