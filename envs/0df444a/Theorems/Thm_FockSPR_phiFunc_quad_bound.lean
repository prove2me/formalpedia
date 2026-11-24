-- Prove2me | Theorems.Thm_FockSPR_phiFunc_quad_bound
-- name    : FockSPR.phiFunc_quad_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:10.180336+00:00
-- url     : https://prove2.me/theorems/1899c551-be41-479d-9d3e-8a8fb7944a52
-- title:
--   Fock SPR: phi Func quad bound
-- statement:
--   The Fock SPR construction uses the phi Func quad bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LaplaceFactorial.lean#L159-L163
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LaplaceFactorial.lean#L159-L163

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

theorem FockSPR.phiFunc_quad_bound {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    phiFunc n r ≤ phiFunc n (rStar n) - (r - rStar n) ^ 2 := by sorry
