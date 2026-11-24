-- Prove2me | Theorems.Thm_FockSPR_gaussian_integral_const_add_polyEval
-- name    : FockSPR.gaussian_integral_const_add_polyEval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:05:19.457283+00:00
-- url     : https://prove2.me/theorems/77babf9e-dbb0-4833-b3dc-fa67fb1c87ca
-- title:
--   Fock SPR: gaussian integral const add poly Eval
-- statement:
--   The Fock SPR construction uses the gaussian integral const add poly Eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LocalCore.lean#L797-L965
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LocalCore.lean#L797-L965

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_MainTheorem
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCore
set_option autoImplicit true
@[expose] public section
public section
open FockSPR MeasureTheory Complex Real Polynomial Finset
open scoped ENNReal ComplexConjugate
noncomputable section
open FockSPR

theorem FockSPR.gaussian_integral_const_add_polyEval {D : ℕ} (a : Fin D → ℂ) (c : ℂ) :
    (1 / Real.pi) * ∫ z : ℂ, ‖c + polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      ‖c‖ ^ 2 + fockNormSq a := by sorry
