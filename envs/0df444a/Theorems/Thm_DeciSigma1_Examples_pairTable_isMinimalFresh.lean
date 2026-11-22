-- Prove2me | Theorems.Thm_DeciSigma1_Examples_pairTable_isMinimalFresh
-- name    : DeciSigma1.Examples.pairTable_isMinimalFresh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:07:21.470767+00:00
-- url     : https://prove2.me/theorems/8b56c753-f306-4271-a93c-5ace7a93d0d9
-- title:
--   Examples: pair Table is Minimal Fresh
-- statement:
--   A minimal fresh pair with an empty coordinate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L85-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L85-L85

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Readers
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Readers DeciSigma1.Constraints DeciSigma1.Full DeciSigma1.Full.Reduction

theorem DeciSigma1.Examples.pairTable_isMinimalFresh : IsMinimalFresh pairTable ![[1], []] := by sorry
