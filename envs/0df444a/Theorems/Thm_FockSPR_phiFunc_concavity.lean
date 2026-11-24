-- Prove2me | Theorems.Thm_FockSPR_phiFunc_concavity
-- name    : FockSPR.phiFunc_concavity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:15:09.953571+00:00
-- url     : https://prove2.me/theorems/6f1d6e9e-374e-4383-ae18-52761923e80b
-- title:
--   Fock SPR: phi Func concavity
-- statement:
--   The Fock SPR construction uses the phi Func concavity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LaplaceFactorial.lean#L79-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LaplaceFactorial.lean#L79-L93

module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LaplaceFactorial
set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory Set
noncomputable section
open FockSPR

theorem FockSPR.phiFunc_concavity {n : ℕ} (hn : 1 ≤ n) :
    StrictConcaveOn ℝ (Ioi 0) (phiFunc n) := by sorry
