-- Prove2me | Theorems.Thm_DeciSigma1_Examples_fixedPoint_regular
-- name    : DeciSigma1.Examples.fixedPoint_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:28:32.47697+00:00
-- url     : https://prove2.me/theorems/9e263dc5-3660-4dfc-9b79-48babe6da2d8
-- title:
--   Examples: fixed Point regular
-- statement:
--   The infinite tree `f(f(…))` is regular and satisfies `x = f(x)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L90-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Sentences.lean#L90-L99

module
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Sentences
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Semantics DeciSigma1.Full.Models

theorem DeciSigma1.Examples.fixedPoint_regular : fixedPoint.HoldsIn RegularTop (fun _ => true) := by sorry
