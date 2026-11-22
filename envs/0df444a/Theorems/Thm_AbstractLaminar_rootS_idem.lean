-- Prove2me | Theorems.Thm_AbstractLaminar_rootS_idem
-- name    : AbstractLaminar.rootS_idem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:16.827921+00:00
-- url     : https://prove2.me/theorems/c296818c-42c3-44d6-892d-d5a8dde39855
-- title:
--   Abstract Laminar: root S idem
-- statement:
--   Root is idempotent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L207-L213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L207-L213

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

theorem AbstractLaminar.rootS_idem {f : ι} (hf : f ∈ Sstrict fam a b) :
    rootS fam a b (rootS fam a b f) = rootS fam a b f := by sorry
