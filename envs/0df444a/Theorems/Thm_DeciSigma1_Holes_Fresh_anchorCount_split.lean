-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_anchorCount_split
-- name    : DeciSigma1.Holes.Fresh.anchorCount_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:19.585304+00:00
-- url     : https://prove2.me/theorems/4a6b2cf1-dcfc-488a-8dea-19322c03691b
-- title:
--   Fresh: anchor Count split
-- statement:
--   The Fresh construction uses the anchor Count split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L162-L174
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L162-L174

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

theorem DeciSigma1.Holes.Fresh.anchorCount_split {s p e : ℕ} (h1 : s ≤ p) (h2 : p ≤ e) :
    anchorCount A s e = anchorCount A s p + anchorCount A p e := by sorry
