-- Prove2me | Theorems.Thm_DeciSigma1_Examples_crossReader_not_hole
-- name    : DeciSigma1.Examples.crossReader_not_hole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:07:29.921227+00:00
-- url     : https://prove2.me/theorems/2f5c09b4-48aa-4635-a018-1eeadd23d17d
-- title:
--   Examples: cross Reader not hole
-- statement:
--   The pair of empty words is not a hole: since `x₀ ≤ y₁`, the channel from the first coordinate
--   to the second carries an admitted pair at the empty word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L108-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L108-L108

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Readers
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Readers DeciSigma1.Constraints DeciSigma1.Full DeciSigma1.Full.Reduction

theorem DeciSigma1.Examples.crossReader_not_hole : ¬ crossReader.IsHole ![[], []] := by sorry
