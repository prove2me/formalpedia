-- Prove2me | Theorems.Thm_AbstractLaminar_rootS_window
-- name    : AbstractLaminar.rootS_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:47.69142+00:00
-- url     : https://prove2.me/theorems/6ad81fa5-8689-4e94-a2e2-9b9f44a92c17
-- title:
--   Abstract Laminar: root S window
-- statement:
--   The Abstract Laminar construction uses the root S window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L173-L175
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L173-L175

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

theorem AbstractLaminar.rootS_window {f : ι} (hf : f ∈ Sstrict fam a b) :
    a ≤ fam.lo (rootS fam a b f) ∧ fam.hi (rootS fam a b f) ≤ b := by sorry
