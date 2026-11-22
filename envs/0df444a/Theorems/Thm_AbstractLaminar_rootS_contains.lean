-- Prove2me | Theorems.Thm_AbstractLaminar_rootS_contains
-- name    : AbstractLaminar.rootS_contains
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:14.982242+00:00
-- url     : https://prove2.me/theorems/610cbe41-5d1c-4f0c-b2ce-17d03b9d1788
-- title:
--   Abstract Laminar: root S contains
-- statement:
--   The Abstract Laminar construction uses the root S contains property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L181-L183
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L181-L183

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

theorem AbstractLaminar.rootS_contains {f : ι} (hf : f ∈ Sstrict fam a b) :
    fam.lo (rootS fam a b f) ≤ fam.lo f ∧ fam.hi f ≤ fam.hi (rootS fam a b f) := by sorry
