-- Prove2me | Theorems.Thm_DeciSigma1_Examples_freshTable_has_shorter_fresh_dominator
-- name    : DeciSigma1.Examples.freshTable_has_shorter_fresh_dominator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:07:08.208342+00:00
-- url     : https://prove2.me/theorems/0abe9887-d2a6-4587-8f7f-449ed33323d2
-- title:
--   Examples: fresh Table has shorter fresh dominator
-- statement:
--   The word `01` has the strictly shorter fresh dominator `1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L78-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L78-L79

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Readers
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Readers DeciSigma1.Constraints DeciSigma1.Full DeciSigma1.Full.Reduction

theorem DeciSigma1.Examples.freshTable_has_shorter_fresh_dominator : FreshDominates freshTable ![[1]] ![[0, 1]] ∧
    totalLength ![[1]] < totalLength (![[0, 1]] : Fin 1 → List (Fin 2)) := by sorry
