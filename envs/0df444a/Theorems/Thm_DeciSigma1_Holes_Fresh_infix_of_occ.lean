-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_infix_of_occ
-- name    : DeciSigma1.Holes.Fresh.infix_of_occ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:11.247079+00:00
-- url     : https://prove2.me/theorems/b1090cae-71eb-4fff-91aa-23169186f539
-- title:
--   Fresh: infix of occ
-- statement:
--   An occurrence of `v` inside an occurrence of `u` in the same word makes `v` a factor of `u`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L91-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L91-L100

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

theorem DeciSigma1.Holes.Fresh.infix_of_occ {i j : ℕ} (hu : u <+: x.drop i) (hv : v <+: x.drop j) (hij : i ≤ j)
    (hlen : j + v.length ≤ i + u.length) : v <:+: u := by sorry
