-- Prove2me | Theorems.Thm_BSLambda_LLL_exists_gate_labelling
-- name    : BSLambda.LLL.exists_gate_labelling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:09:12.643728+00:00
-- url     : https://prove2.me/theorems/8daf990d-8319-4a05-bd21-e1a1d07919ec
-- title:
--   LLL: exists gate labelling
-- statement:
--   **Section 10**: a gate labelling satisfying the local certificate-list conditions
--   (L1) and (L2) exists.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L873-L882
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L873-L882

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}

theorem BSLambda.LLL.exists_gate_labelling [NeZero r] (hk : Fintype.card ι = 14011)
    (hT : IsDRTournamentWith Arc 7005 3502) (hr : r = 144) :
    ∃ γ : ι → ι → Fin r,
      (∀ h x, (cert Arc γ h).Sat x →
        (Finset.univ.filter fun j => j ≠ h ∧ (cert Arc γ j).dist x = 1).card ≤ 3) ∧
      (∀ h x, (cert Arc γ h).Sat x →
        (Finset.univ.filter fun j => j ≠ h ∧ (cert Arc γ j).dist x ≤ 2).card ≤ 7) := by sorry
