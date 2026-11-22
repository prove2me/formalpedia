-- Prove2me | Theorems.Thm_AbstractLaminar_column_sep
-- name    : AbstractLaminar.column_sep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:33.874219+00:00
-- url     : https://prove2.me/theorems/40fd37ac-3fbd-4541-aa2a-ead97d43a136
-- title:
--   Abstract Laminar: column sep
-- statement:
--   **COLUMN-SEPARATION (abstract).** For a saturated window `(a,b]` with a top edge `e0`, every
--       root has column `≠ col e0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L245-L333
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L245-L333

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

theorem AbstractLaminar.column_sep {a b : ℕ} (hab : a < b) (hsat : N fam a b = b - a)
    {e0 : ι} (he0E : e0 ∈ fam.E) (he0lo : fam.lo e0 = a) (he0hi : fam.hi e0 = b) :
    ∀ r ∈ Roots fam a b, fam.col r ≠ fam.col e0 := by sorry
