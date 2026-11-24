-- Prove2me | Theorems.Thm_FockSPR_exp_phi_le_factorial
-- name    : FockSPR.exp_phi_le_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:08.802429+00:00
-- url     : https://prove2.me/theorems/8f18fc77-4ae6-422d-b7c5-6ff9ac6dd765
-- title:
--   Fock SPR: exp phi le factorial
-- statement:
--   The Fock SPR construction uses the exp phi le factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LaplaceFactorial.lean#L223-L240
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/LaplaceFactorial.lean#L223-L240

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

theorem FockSPR.exp_phi_le_factorial {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (phiFunc n (rStar n)) ≤
    Real.exp (1 / 4) * (Nat.factorial n : ℝ) / 2 := by sorry
