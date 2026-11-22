-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_of_suffix_of_le
-- name    : DeciSigma1.Holes.Fresh.suffix_of_suffix_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:06.395481+00:00
-- url     : https://prove2.me/theorems/731c2e38-28aa-43c6-85da-cd028156df73
-- title:
--   Fresh: suffix of suffix of le
-- statement:
--   Two suffixes of one word, the shorter is a suffix of the longer.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L119-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L119-L120

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

theorem DeciSigma1.Holes.Fresh.suffix_of_suffix_of_le {w : List α} (hu : u <:+ w) (hv : v <:+ w)
    (h : u.length ≤ v.length) : u <:+ v := by sorry
