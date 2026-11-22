-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
-- name    : DeciSigma1.Holes.Fresh.length_reversedBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:24.957804+00:00
-- url     : https://prove2.me/theorems/7fc26039-dd90-4e11-863a-a696021d2ca2
-- title:
--   Fresh: length reversed Blocks
-- statement:
--   The Fresh construction uses the length reversed Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L402-L403
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L402-L403

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

theorem DeciSigma1.Holes.Fresh.length_reversedBlocks (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) :
    (reversedBlocks W t o).length = lowerBlockCount W t o := by sorry
