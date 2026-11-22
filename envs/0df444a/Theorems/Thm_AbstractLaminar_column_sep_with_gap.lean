-- Prove2me | Theorems.Thm_AbstractLaminar_column_sep_with_gap
-- name    : AbstractLaminar.column_sep_with_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:32.171776+00:00
-- url     : https://prove2.me/theorems/a1aac7a4-7423-44e2-a640-b8b551c2a310
-- title:
--   Abstract Laminar: column sep with gap
-- statement:
--   **DIRECTIONAL COLUMN-SEPARATION (abstract).**  As `column_sep`, but exposes the gap `g`
--       together with the run-direction columns: left roots (top below the gap) have `col e0 < col r`,
--       right roots (bottom above the gap) have `col r < col e0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L338-L412
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L338-L412

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

theorem AbstractLaminar.column_sep_with_gap {a b : ℕ} (hab : a < b) (hsat : N fam a b = b - a)
    {e0 : ι} (he0E : e0 ∈ fam.E) (he0lo : fam.lo e0 = a) (he0hi : fam.hi e0 = b) :
    ∃ g, a < g ∧ g ≤ b ∧ (∀ r ∈ Roots fam a b, ¬ (fam.lo r < g ∧ g ≤ fam.hi r)) ∧
      (∀ r ∈ Roots fam a b, fam.hi r < g → fam.col e0 < fam.col r) ∧
      (∀ r ∈ Roots fam a b, g ≤ fam.lo r → fam.col r < fam.col e0) := by sorry
