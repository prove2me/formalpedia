-- Prove2me | Theorems.Thm_FockSPR_centeredPolynomial_eval_zero
-- name    : FockSPR.centeredPolynomial_eval_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:15:35.056495+00:00
-- url     : https://prove2.me/theorems/7cc81ddd-4da0-4a7b-bc44-4cc28f2eda9c
-- title:
--   Fock SPR: centered Polynomial eval zero
-- statement:
--   The centered polynomial has zero constant term.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant.lean#L40-L41
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant.lean#L40-L41

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Local
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCore
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalHelpers
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant
set_option autoImplicit true
@[expose] public section
public section
open FockSPR MeasureTheory Complex Real Polynomial
noncomputable section
open FockSPR

theorem FockSPR.centeredPolynomial_eval_zero (p : Polynomial ℂ) :
    (centeredPolynomial p).eval 0 = 0 := by sorry
