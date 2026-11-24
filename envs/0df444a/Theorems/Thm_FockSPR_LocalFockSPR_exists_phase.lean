-- Prove2me | Theorems.Thm_FockSPR_LocalFockSPR_exists_phase
-- name    : FockSPR.LocalFockSPR_exists_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:15:29.538823+00:00
-- url     : https://prove2.me/theorems/1641bc72-29f0-4353-8f04-582697e1f1d8
-- title:
--   Fock SPR: Local Fock SPR exists phase
-- statement:
--   The Fock SPR construction uses the Local Fock SPR exists phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/Local.lean#L66-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/Local.lean#L66-L75

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

theorem FockSPR.LocalFockSPR_exists_phase
    (p : Polynomial ℂ)
    (hsmall :
      (1 / Real.pi) * ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
        (1 / 4601 : ℝ) ^ 2) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      ∫ z : ℂ, ‖w * ((1 : ℂ) + p.eval z) - 1‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
        23003 ^ 2 *
          ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) := by sorry
