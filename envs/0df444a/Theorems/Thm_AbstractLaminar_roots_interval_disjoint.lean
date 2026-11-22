-- Prove2me | Theorems.Thm_AbstractLaminar_roots_interval_disjoint
-- name    : AbstractLaminar.roots_interval_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:17.109192+00:00
-- url     : https://prove2.me/theorems/21630975-de8d-47df-8cea-89ef5ec581b5
-- title:
--   Abstract Laminar: roots interval disjoint
-- statement:
--   Distinct roots have disjoint half-open level-intervals.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L326-L337
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L326-L337

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

theorem AbstractLaminar.roots_interval_disjoint {r r' : ι} (hr : r ∈ Roots fam a b) (hr' : r' ∈ Roots fam a b)
    (hne : r ≠ r') : fam.hi r ≤ fam.lo r' ∨ fam.hi r' ≤ fam.lo r := by sorry
