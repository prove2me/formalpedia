-- Prove2me | Theorems.Thm_DeciSigma1_Examples_crossReader_hole
-- name    : DeciSigma1.Examples.crossReader_hole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:17:28.616593+00:00
-- url     : https://prove2.me/theorems/28aa0cea-3c99-4c69-a2e6-82fe31454151
-- title:
--   Examples: cross Reader hole
-- statement:
--   The pair of words `([], [0])` is a hole.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L111-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L111-L111

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Readers
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Readers DeciSigma1.Constraints DeciSigma1.Full DeciSigma1.Full.Reduction

theorem DeciSigma1.Examples.crossReader_hole : crossReader.IsHole ![[], [0]] := by sorry
