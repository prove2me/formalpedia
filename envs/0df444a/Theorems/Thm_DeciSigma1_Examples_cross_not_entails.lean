-- Prove2me | Theorems.Thm_DeciSigma1_Examples_cross_not_entails
-- name    : DeciSigma1.Examples.cross_not_entails
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:07:49.936864+00:00
-- url     : https://prove2.me/theorems/2ad2ee44-c886-4e8d-8c97-5c80dbc3ab6d
-- title:
--   Examples: cross not entails
-- statement:
--   Hence `x₀ ≤ y₁` does not entail `x₀ ≤ y₀ ∨ x₁ ≤ y₁`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L114-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean#L114-L118

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Readers
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Readers DeciSigma1.Constraints DeciSigma1.Full DeciSigma1.Full.Reduction

theorem DeciSigma1.Examples.cross_not_entails :
    ¬ DisjEntailsIn (fun _ => True) (fun _ => false) crossSystem crossQueries := by sorry
