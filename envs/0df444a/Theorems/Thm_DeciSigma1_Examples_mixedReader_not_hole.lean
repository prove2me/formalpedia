-- Prove2me | Theorems.Thm_DeciSigma1_Examples_mixedReader_not_hole
-- name    : DeciSigma1.Examples.mixedReader_not_hole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:07:16.700463+00:00
-- url     : https://prove2.me/theorems/449abd8a-9bb1-49ce-a239-870a6eadfcb5
-- title:
--   Examples: mixed Reader not hole
-- statement:
--   The admitted pair `(2, 1)` lies on a channel: the target word `00` is a prefix of the host word
--   `000` after its first letter, where the host is in state `2` and the target in state `1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L69-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L69-L69

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Readers
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Readers DeciSigma1.Constraints DeciSigma1.Full DeciSigma1.Full.Reduction

theorem DeciSigma1.Examples.mixedReader_not_hole : ¬ mixedReader.IsHole ![[0, 0, 0], [0, 0]] := by sorry
