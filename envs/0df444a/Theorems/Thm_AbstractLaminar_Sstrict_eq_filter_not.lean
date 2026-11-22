-- Prove2me | Theorems.Thm_AbstractLaminar_Sstrict_eq_filter_not
-- name    : AbstractLaminar.Sstrict_eq_filter_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:19.675122+00:00
-- url     : https://prove2.me/theorems/9da038e1-1b7d-4708-9bd8-08af009d97c2
-- title:
--   Abstract Laminar: Sstrict eq filter not
-- statement:
--   `Sstrict` is the complementary filter to `topEdges`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L306-L316
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L306-L316

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

theorem AbstractLaminar.Sstrict_eq_filter_not :
    Sstrict fam a b = (contained fam a b).filter (fun e => ¬ (fam.lo e = a ∧ fam.hi e = b)) := by sorry
