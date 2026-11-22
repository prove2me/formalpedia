-- Prove2me | Theorems.Thm_CriticalPortraits_mem_beta_iff
-- name    : CriticalPortraits.mem_beta_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:58.153114+00:00
-- url     : https://prove2.me/theorems/fe8907b7-b5f4-40db-80c8-a5da4865ebed
-- title:
--   Critical Portraits: mem beta iff
-- statement:
--   The Critical Portraits construction uses the mem beta iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L728-L730
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L728-L730

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

theorem CriticalPortraits.mem_beta_iff {d m : ℕ} {U : Finset (ZMod (d * m))} {S : Finset (ZMod (d * m))} :
    S ∈ beta U ↔ ∃ v ∈ bVerts U, betaBlock U v = S := by sorry
