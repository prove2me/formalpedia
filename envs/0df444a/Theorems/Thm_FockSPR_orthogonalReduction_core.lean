-- Prove2me | Theorems.Thm_FockSPR_orthogonalReduction_core
-- name    : FockSPR.orthogonalReduction_core
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:27:11.246143+00:00
-- url     : https://prove2.me/theorems/56b6db65-81c3-4949-abd7-82003f310500
-- title:
--   Fock SPR: orthogonal Reduction core
-- statement:
--   The centered core estimate, stated as a reusable theorem for the paper.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant.lean#L49-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant.lean#L49-L58

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

theorem FockSPR.orthogonalReduction_core
    (p : Polynomial ℂ)
    (hp_real : Complex.im (p.eval 0) = 0)
    (hsmall :
      (1 / Real.pi) * ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
        (1 / 4601 : ℝ) ^ 2) :
    ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
      23003 ^ 2 *
        ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) := by sorry
