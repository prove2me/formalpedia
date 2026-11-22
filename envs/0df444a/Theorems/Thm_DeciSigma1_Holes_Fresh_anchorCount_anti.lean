-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_anchorCount_anti
-- name    : DeciSigma1.Holes.Fresh.anchorCount_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:23.290939+00:00
-- url     : https://prove2.me/theorems/f5e98668-446a-4aeb-a75c-06b87e149ffd
-- title:
--   Fresh: anchor Count anti
-- statement:
--   The Fresh construction uses the anchor Count anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L176-L178
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L176-L178

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

theorem DeciSigma1.Holes.Fresh.anchorCount_anti {p q e : ℕ} (h : q ≤ p) : anchorCount A p e ≤ anchorCount A q e := by sorry
