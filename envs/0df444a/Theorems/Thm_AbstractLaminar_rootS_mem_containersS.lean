-- Prove2me | Theorems.Thm_AbstractLaminar_rootS_mem_containersS
-- name    : AbstractLaminar.rootS_mem_containersS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:14.536306+00:00
-- url     : https://prove2.me/theorems/daba6c79-504b-4704-ba8e-409243f187e3
-- title:
--   Abstract Laminar: root S mem containers S
-- statement:
--   The Abstract Laminar construction uses the root S mem containers S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L151-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L151-L155

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

theorem AbstractLaminar.rootS_mem_containersS {a b : ℕ} {f : ι} (hf : f ∈ Sstrict fam a b) :
    rootS fam a b f ∈ containersS fam a b f := by sorry
