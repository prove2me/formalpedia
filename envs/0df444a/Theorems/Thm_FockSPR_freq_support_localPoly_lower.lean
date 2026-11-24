-- Prove2me | Theorems.Thm_FockSPR_freq_support_localPoly_lower
-- name    : FockSPR.freq_support_localPoly_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:14:45.398807+00:00
-- url     : https://prove2.me/theorems/818fba3d-330e-4d94-918d-ed67cf82559d
-- title:
--   Fock SPR: freq support local Poly lower
-- statement:
--   Frequencies of `V_j` are all ≥ `(j−M)²` when `j ≥ M + 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L306-L312
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/BlockDecomposition.lean#L306-L312

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
set_option autoImplicit true
@[expose] public section
public section
open Finset Nat Real MeasureTheory
noncomputable section
open FockSPR

theorem FockSPR.freq_support_localPoly_lower {M j : ℕ} (_hM : 1 ≤ M) (hj : M + 1 ≤ j) :
    ∀ n ∈ freqBlock ℓ,
      ℓ ∈ Finset.Icc (max 1 (j - M)) (j + M) → (j - M) ^ 2 ≤ n := by sorry
