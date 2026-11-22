-- Prove2me | Theorems.Thm_AbstractLaminar_edge_tight_of_saturated
-- name    : AbstractLaminar.edge_tight_of_saturated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:31.413652+00:00
-- url     : https://prove2.me/theorems/9b3d2535-739b-4f51-9e05-aec72d997fe5
-- title:
--   Abstract Laminar: edge tight of saturated
-- statement:
--   **Every edge is tight.** If the window `(a,b]` is saturated, then every edge contained in
--       it has a saturated own-window (`N(lo e, hi e) = hi e - lo e`, i.e. `g(e) = h(e) - 1`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L108-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L108-L134

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

theorem AbstractLaminar.edge_tight_of_saturated :
    ∀ w : ℕ, ∀ a b : ℕ, b - a = w → N fam a b = b - a →
      ∀ e ∈ contained fam a b, N fam (fam.lo e) (fam.hi e) = fam.hi e - fam.lo e := by sorry
