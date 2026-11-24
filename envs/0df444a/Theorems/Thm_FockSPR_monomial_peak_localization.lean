-- Prove2me | Theorems.Thm_FockSPR_monomial_peak_localization
-- name    : FockSPR.monomial_peak_localization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:54.142675+00:00
-- url     : https://prove2.me/theorems/2ba7848a-6e70-43b1-8fb0-b86c6b036ec1
-- title:
--   Fock SPR: monomial peak localization
-- statement:
--   The Fock SPR construction uses the monomial peak localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L347-L366
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L347-L366

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
set_option autoImplicit true
@[expose] public section
public section
open Finset Nat Real MeasureTheory
noncomputable section
open FockSPR

theorem FockSPR.monomial_peak_localization {n ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hn : n ∈ freqBlock ℓ) :
    (ℓ : ℝ) < Real.sqrt (n + 1 / 2) ∧
      Real.sqrt (n + 1 / 2) < (ℓ + 1 : ℝ) := by sorry
