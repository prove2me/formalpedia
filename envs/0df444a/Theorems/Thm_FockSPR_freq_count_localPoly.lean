-- Prove2me | Theorems.Thm_FockSPR_freq_count_localPoly
-- name    : FockSPR.freq_count_localPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:14:48.655129+00:00
-- url     : https://prove2.me/theorems/8b1ba536-f697-4e21-99c1-453907ccd5f4
-- title:
--   Fock SPR: freq count local Poly
-- statement:
--   The number of frequencies in `V_j` for `j ≥ M + 1` is `(2M+1)(2j+1)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L325-L336
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L325-L336

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
set_option autoImplicit true
@[expose] public section
public section
open Finset Nat Real MeasureTheory
noncomputable section
open FockSPR

theorem FockSPR.freq_count_localPoly {M j : ℕ} (hM : 1 ≤ M) (hj : M + 1 ≤ j) :
    (Finset.Icc (max 1 (j - M)) (j + M)).sum
      (fun ℓ => (freqBlock ℓ).card) =
      (2 * M + 1) * (2 * j + 1) := by sorry
