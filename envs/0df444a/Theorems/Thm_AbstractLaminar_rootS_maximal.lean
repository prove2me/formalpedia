-- Prove2me | Theorems.Thm_AbstractLaminar_rootS_maximal
-- name    : AbstractLaminar.rootS_maximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:51.504218+00:00
-- url     : https://prove2.me/theorems/cf6379b2-64f1-4d84-836e-5d4ecbea632f
-- title:
--   Abstract Laminar: root S maximal
-- statement:
--   The root is maximal among strict edges.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L193-L204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L193-L204

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

theorem AbstractLaminar.rootS_maximal {f : ι} (hf : f ∈ Sstrict fam a b)
    {g : ι} (hg : g ∈ Sstrict fam a b)
    (h1 : fam.lo g ≤ fam.lo (rootS fam a b f)) (h2 : fam.hi (rootS fam a b f) ≤ fam.hi g) :
    fam.lo g = fam.lo (rootS fam a b f) ∧ fam.hi g = fam.hi (rootS fam a b f) := by sorry
