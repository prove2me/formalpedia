-- Prove2me | Theorems.Thm_AbstractLaminar_rootS_width_lt
-- name    : AbstractLaminar.rootS_width_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:50.630907+00:00
-- url     : https://prove2.me/theorems/ae2b4528-08f5-40a8-958b-f32f09ed2ac1
-- title:
--   Abstract Laminar: root S width lt
-- statement:
--   The root's width is strictly less than the window's width.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L186-L190
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L186-L190

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

theorem AbstractLaminar.rootS_width_lt {f : ι} (hf : f ∈ Sstrict fam a b) :
    fam.hi (rootS fam a b f) - fam.lo (rootS fam a b f) < b - a := by sorry
