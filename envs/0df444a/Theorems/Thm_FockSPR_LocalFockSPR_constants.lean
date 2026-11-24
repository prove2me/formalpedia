-- Prove2me | Theorems.Thm_FockSPR_LocalFockSPR_constants
-- name    : FockSPR.LocalFockSPR_constants
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:15:31.236203+00:00
-- url     : https://prove2.me/theorems/36343ee8-155f-4615-829f-9f4329d87b66
-- title:
--   Fock SPR: Local Fock SPR constants
-- statement:
--   The Fock SPR construction uses the Local Fock SPR constants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/Local.lean#L54-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/Local.lean#L54-L64

module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalHelpers
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Local
set_option autoImplicit true
@[expose] public section
public section
open FockSPR MeasureTheory Complex Real Polynomial
noncomputable section
open FockSPR

theorem FockSPR.LocalFockSPR_constants :
    ∃ δ M : ℝ,
      δ = (1 / 4601 : ℝ) ∧
      M = (23003 : ℝ) ∧
      ∀ p : Polynomial ℂ,
        (1 / Real.pi) * ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤ δ ^ 2 →
          ∃ w : ℂ, ‖w‖ = 1 ∧
            ∫ z : ℂ, ‖w * (1 + p.eval z) - 1‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
              M ^ 2 * ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) := by sorry
