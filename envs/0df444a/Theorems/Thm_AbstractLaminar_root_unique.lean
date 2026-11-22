-- Prove2me | Theorems.Thm_AbstractLaminar_root_unique
-- name    : AbstractLaminar.root_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:49.013832+00:00
-- url     : https://prove2.me/theorems/f80964dc-423b-4ead-b1c5-b9501cb5b002
-- title:
--   Abstract Laminar: root unique
-- statement:
--   Uniqueness: two roots that both contain `g`'s interval coincide.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L233-L253
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L233-L253

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

theorem AbstractLaminar.root_unique {r r' : ι} (hr : r ∈ Roots fam a b) (hr' : r' ∈ Roots fam a b)
    {g : ι} (hg : g ∈ fam.E)
    (h1 : fam.lo r ≤ fam.lo g) (h2 : fam.hi g ≤ fam.hi r)
    (h1' : fam.lo r' ≤ fam.lo g) (h2' : fam.hi g ≤ fam.hi r') :
    r = r' := by sorry
