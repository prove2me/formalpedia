-- Prove2me | Theorems.Thm_AbstractLaminar_roots_Ioc_disjoint
-- name    : AbstractLaminar.roots_Ioc_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:17.535112+00:00
-- url     : https://prove2.me/theorems/f7b9d1b5-c2f3-4c7f-959e-76a369ac48ff
-- title:
--   Abstract Laminar: roots Ioc disjoint
-- statement:
--   The `Finset.Ioc` intervals of distinct roots are disjoint.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L340-L345
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L340-L345

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
set_option autoImplicit true
@[expose] public section
public section
open AbstractLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
variable {a b : ℕ}

theorem AbstractLaminar.roots_Ioc_disjoint :
    (Roots fam a b : Set ι).PairwiseDisjoint (fun r => Finset.Ioc (fam.lo r) (fam.hi r)) := by sorry
