-- Prove2me | Theorems.Thm_AbstractLaminar_N_split
-- name    : AbstractLaminar.N_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:19.184215+00:00
-- url     : https://prove2.me/theorems/cd51ff18-6c22-48d6-9386-84382a188250
-- title:
--   Abstract Laminar: N split
-- statement:
--   `N = #topEdges + #Sstrict`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L319-L323
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L319-L323

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

theorem AbstractLaminar.N_split : N fam a b = (topEdges fam a b).card + (Sstrict fam a b).card := by sorry
