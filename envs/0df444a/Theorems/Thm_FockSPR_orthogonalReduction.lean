-- Prove2me | Theorems.Thm_FockSPR_orthogonalReduction
-- name    : FockSPR.orthogonalReduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:15:53.835934+00:00
-- url     : https://prove2.me/theorems/fe4fd8b4-9039-4c50-92dd-569e78037a1b
-- title:
--   Fock SPR: orthogonal Reduction
-- statement:
--   The paper-friendly orthogonal reduction step: split off the constant term.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant.lean#L44-L46
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant.lean#L44-L46

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

theorem FockSPR.orthogonalReduction (p : Polynomial ℂ) :
    p = centeredPolynomial p + Polynomial.C (p.eval 0) := by sorry
