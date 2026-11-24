-- Prove2me | Theorems.Thm_FockSPR_LocalFockSPR_of_small_norm
-- name    : FockSPR.LocalFockSPR_of_small_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:05:23.845296+00:00
-- url     : https://prove2.me/theorems/7add81e6-b996-4505-9d26-37399f6174e2
-- title:
--   Fock SPR: Local Fock SPR of small norm
-- statement:
--   The Fock SPR construction uses the Local Fock SPR of small norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LocalCore.lean#L1449-L1637
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LocalCore.lean#L1449-L1637

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

theorem FockSPR.LocalFockSPR_of_small_norm
    (p : Polynomial ℂ)
    (hp_real : Complex.im (p.eval 0) = 0)
    (hsmall :
      (1 / Real.pi) * ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
        (1 / 4601 : ℝ) ^ 2) :
    ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
      23003 ^ 2 *
        ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) := by sorry
