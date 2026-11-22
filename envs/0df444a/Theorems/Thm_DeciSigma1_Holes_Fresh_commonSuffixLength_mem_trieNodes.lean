-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_commonSuffixLength_mem_trieNodes
-- name    : DeciSigma1.Holes.Fresh.commonSuffixLength_mem_trieNodes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:29.60032+00:00
-- url     : https://prove2.me/theorems/4ecbfd37-d6e0-4551-858a-c16f745882bc
-- title:
--   Fresh: common Suffix Length mem trie Nodes
-- statement:
--   The Fresh construction uses the common Suffix Length mem trie Nodes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L506-L508
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L506-L508

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
variable {α : Type} [DecidableEq α] {k : ℕ}

theorem DeciSigma1.Holes.Fresh.commonSuffixLength_mem_trieNodes {W : Fin k → List α} {t : ℕ} (Z : List (List α))
    {Y : List (List α)} (hY : Y ∈ upperParses W t) : commonSuffixLength Z Y ∈ trieNodes W t Z := by sorry
