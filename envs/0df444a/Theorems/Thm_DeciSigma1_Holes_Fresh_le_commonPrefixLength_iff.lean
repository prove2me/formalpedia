-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_le_commonPrefixLength_iff
-- name    : DeciSigma1.Holes.Fresh.le_commonPrefixLength_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:53.535658+00:00
-- url     : https://prove2.me/theorems/9b329698-7249-48b3-b104-b23cb7b17b05
-- title:
--   Fresh: le common Prefix Length iff
-- statement:
--   The Fresh construction uses the le common Prefix Length iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L64-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L64-L81

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
variable {β : Type} [DecidableEq β]

theorem DeciSigma1.Holes.Fresh.le_commonPrefixLength_iff {A B : List β} {d : ℕ} :
    d ≤ commonPrefixLength A B ↔ d ≤ A.length ∧ d ≤ B.length ∧ A.take d = B.take d := by sorry
