-- Prove2me | Theorems.Thm_DeciSigma1_Examples_mixedReader_hole
-- name    : DeciSigma1.Examples.mixedReader_hole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:07:11.952557+00:00
-- url     : https://prove2.me/theorems/527501d6-1450-4609-b75c-d0b4b8d29bbc
-- title:
--   Examples: mixed Reader hole
-- statement:
--   The tuple `(000, 1)` is a hole.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L61-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L61-L61

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Readers
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Readers DeciSigma1.Constraints DeciSigma1.Full DeciSigma1.Full.Reduction

theorem DeciSigma1.Examples.mixedReader_hole : mixedReader.IsHole mixedWords := by sorry
