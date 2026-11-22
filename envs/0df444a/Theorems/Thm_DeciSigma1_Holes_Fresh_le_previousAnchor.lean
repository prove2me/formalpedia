-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_le_previousAnchor
-- name    : DeciSigma1.Holes.Fresh.le_previousAnchor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:09.772247+00:00
-- url     : https://prove2.me/theorems/2a3271c7-3a33-4607-8c5a-bd87fb7e3207
-- title:
--   Fresh: le previous Anchor
-- statement:
--   The Fresh construction uses the le previous Anchor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L147-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L147-L148

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

theorem DeciSigma1.Holes.Fresh.le_previousAnchor {p q : ℕ} (hq : q ∈ A) (hqp : q < p) : q ≤ previousAnchor A p := by sorry
