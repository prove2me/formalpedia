-- Prove2me | Theorems.Thm_AbstractLaminar_exists_gap
-- name    : AbstractLaminar.exists_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:03.119979+00:00
-- url     : https://prove2.me/theorems/e9d881ba-6b7e-47aa-9b6c-eb9ca8b8ed6a
-- title:
--   Abstract Laminar: exists gap
-- statement:
--   The root level-intervals of a saturated top-edged window miss exactly one level `g*`:
--       there is a unique `g ∈ (a,b]` covered by no root.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L163-L193
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L163-L193

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open AbstractLaminar
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)

theorem AbstractLaminar.exists_gap {a b : ℕ} (hab : a < b) (hsat : N fam a b = b - a)
    (htop : (topEdges fam a b).Nonempty) :
    ∃ g, a < g ∧ g ≤ b ∧ (∀ r ∈ Roots fam a b, ¬ (fam.lo r < g ∧ g ≤ fam.hi r)) := by sorry
