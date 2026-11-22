-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
-- name    : DeciSigma1.Holes.Fresh.length_upperSeq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:26.416749+00:00
-- url     : https://prove2.me/theorems/840d00d4-c1f4-4191-8684-0db41ddf116b
-- title:
--   Fresh: length upper Seq
-- statement:
--   The Fresh construction uses the length upper Seq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L405-L406
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L405-L406

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

theorem DeciSigma1.Holes.Fresh.length_upperSeq (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) :
    (upperParse W t o).length = lowerBlockCount W t o := by sorry
