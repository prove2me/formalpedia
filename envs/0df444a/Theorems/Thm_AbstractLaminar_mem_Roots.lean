-- Prove2me | Theorems.Thm_AbstractLaminar_mem_Roots
-- name    : AbstractLaminar.mem_Roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:15.239151+00:00
-- url     : https://prove2.me/theorems/36761430-9ee7-4dbf-b808-5c5571dfcdff
-- title:
--   Abstract Laminar: mem Roots
-- statement:
--   The Abstract Laminar construction uses the mem Roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L219-L220
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L219-L220

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

theorem AbstractLaminar.mem_Roots {r : ι} : r ∈ Roots fam a b ↔ r ∈ Sstrict fam a b ∧ rootS fam a b r = r := by sorry
