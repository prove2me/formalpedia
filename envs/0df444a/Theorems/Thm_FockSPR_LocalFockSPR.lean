-- Prove2me | Theorems.Thm_FockSPR_LocalFockSPR
-- name    : FockSPR.LocalFockSPR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:09:15.7358+00:00
-- url     : https://prove2.me/theorems/941982a6-67ca-4795-9924-98bc2e0e5f9e
-- title:
--   Fock SPR: Local Fock SPR
-- statement:
--   Fock-space coercivity for complex polynomials with zero constant term.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/MainTheorem.lean#L736-L768
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/MainTheorem.lean#L736-L768

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_AnnulusLocalEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LeakageEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_MainTheorem
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex Real Finset Polynomial
noncomputable section
open FockSPR

theorem FockSPR.LocalFockSPR
    (p : Polynomial ℂ)
    (hp : p.eval 0 = 0) :
    ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
    ≤ 4600 ^ 2 *
    ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2)
    := by sorry
