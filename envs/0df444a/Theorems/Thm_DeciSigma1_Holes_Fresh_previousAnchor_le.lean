-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_le
-- name    : DeciSigma1.Holes.Fresh.previousAnchor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:53.16055+00:00
-- url     : https://prove2.me/theorems/915ec9c6-7e27-4a16-90d0-d8d0e1a44afd
-- title:
--   Fresh: previous Anchor le
-- statement:
--   The Fresh construction uses the previous Anchor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L150-L151
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L150-L151

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {A : Finset ℕ}

theorem DeciSigma1.Holes.Fresh.previousAnchor_le {p s : ℕ} (h : ∀ q ∈ A, q < p → q ≤ s) : previousAnchor A p ≤ s := by sorry
