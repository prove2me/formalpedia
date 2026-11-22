-- Prove2me | Theorems.Thm_AbstractLaminar_root_self_props
-- name    : AbstractLaminar.root_self_props
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:11.505678+00:00
-- url     : https://prove2.me/theorems/cc504b81-51e2-4e8e-8c2b-dae453b44cc3
-- title:
--   Abstract Laminar: root self props
-- statement:
--   The Abstract Laminar construction uses the root self props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L226-L230
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L226-L230

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

theorem AbstractLaminar.root_self_props {r : ι} (hr : r ∈ Roots fam a b) :
    r ∈ fam.E ∧ a ≤ fam.lo r ∧ fam.hi r ≤ b ∧ (fam.lo r ≠ a ∨ fam.hi r ≠ b) := by sorry
