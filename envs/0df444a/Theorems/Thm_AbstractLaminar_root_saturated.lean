-- Prove2me | Theorems.Thm_AbstractLaminar_root_saturated
-- name    : AbstractLaminar.root_saturated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:58.007262+00:00
-- url     : https://prove2.me/theorems/58f22050-2f42-442e-b24f-ba8594d27dd8
-- title:
--   Abstract Laminar: root saturated
-- statement:
--   **Saturation propagates to roots.** If the window `(a,b]` is saturated
--       (`N = b-a`), then every root's subtree is itself saturated.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L63-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L63-L104

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

theorem AbstractLaminar.root_saturated {a b : ℕ} (hsat : N fam a b = b - a) :
    ∀ r ∈ Roots fam a b, N fam (fam.lo r) (fam.hi r) = fam.hi r - fam.lo r := by sorry
