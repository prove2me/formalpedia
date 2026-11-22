-- Prove2me | Theorems.Thm_CriticalPortraits_beta_pairwise_disjoint
-- name    : CriticalPortraits.beta_pairwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:38.838099+00:00
-- url     : https://prove2.me/theorems/4f59b277-67de-467a-ab9e-4f7498efb611
-- title:
--   Critical Portraits: beta pairwise disjoint
-- statement:
--   Distinct blocks of `β U` are disjoint.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L865-L872
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L865-L872

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.beta_pairwise_disjoint {d m : ℕ} {U : Finset (ZMod (d * m))} :
    ∀ A ∈ beta U, ∀ B ∈ beta U, A ≠ B → Disjoint A B := by sorry
