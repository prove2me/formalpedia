-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_le_length_of_mem_trieNodes
-- name    : DeciSigma1.Holes.Fresh.le_length_of_mem_trieNodes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:31.51481+00:00
-- url     : https://prove2.me/theorems/6578bd53-9950-4ffd-8dac-faab8c5cd8ab
-- title:
--   Fresh: le length of mem trie Nodes
-- statement:
--   The Fresh construction uses the le length of mem trie Nodes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L510-L516
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L510-L516

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

theorem DeciSigma1.Holes.Fresh.le_length_of_mem_trieNodes {W : Fin k → List α} {t : ℕ} {Z : List (List α)} {c : ℕ}
    (hc : c ∈ trieNodes W t Z) : c ≤ Z.length := by sorry
