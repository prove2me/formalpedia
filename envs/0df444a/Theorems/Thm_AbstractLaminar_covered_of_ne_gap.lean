-- Prove2me | Theorems.Thm_AbstractLaminar_covered_of_ne_gap
-- name    : AbstractLaminar.covered_of_ne_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:56.928472+00:00
-- url     : https://prove2.me/theorems/5c9f4b1b-5d5d-4808-a486-4f26f585b355
-- title:
--   Abstract Laminar: covered of ne gap
-- statement:
--   Every level in `(a,b]` except the gap `g` (with `a < g ≤ b`) is covered by some root.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L196-L230
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L196-L230

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

theorem AbstractLaminar.covered_of_ne_gap {a b g : ℕ} (htop : (topEdges fam a b).Nonempty)
    (hsat : N fam a b = b - a) (hab : a < b)
    (hg1 : a < g) (hg2 : g ≤ b)
    (hgap : ∀ r ∈ Roots fam a b, ¬ (fam.lo r < g ∧ g ≤ fam.hi r))
    {t : ℕ} (ht1 : a < t) (ht2 : t ≤ b) (htne : t ≠ g) :
    ∃ r ∈ Roots fam a b, fam.lo r < t ∧ t ≤ fam.hi r := by sorry
