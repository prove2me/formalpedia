-- Prove2me | Theorems.Thm_DeciSigma1_Examples_mixedReader_hasMixedMortality
-- name    : DeciSigma1.Examples.mixedReader_hasMixedMortality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:07:15.772047+00:00
-- url     : https://prove2.me/theorems/36b5b939-0cf7-4251-9969-4c0556d344bb
-- title:
--   Examples: mixed Reader has Mixed Mortality
-- statement:
--   The hole has mixed mortality: an immortal and a mortal coordinate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L64-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L64-L65

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Readers
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Readers DeciSigma1.Constraints DeciSigma1.Full DeciSigma1.Full.Reduction

theorem DeciSigma1.Examples.mixedReader_hasMixedMortality : mixedReader.HasMixedMortality mixedWords := by sorry
