-- Prove2me | Theorems.Thm_BSLambda_LLL_card_active_flag_through_ordered_pair
-- name    : BSLambda.LLL.card_active_flag_through_ordered_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:35.317438+00:00
-- url     : https://prove2.me/theorems/cb7dd255-744a-4cbf-92ef-25bcc2a60718
-- title:
--   LLL: card active flag through ordered pair
-- statement:
--   **Section 8.2**: at most `N_1 = N_A + N_B = 214,620,087,510` active flags pass through the
--   ordered pair `u → v`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L627-L640
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L627-L640

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
open scoped Classical

theorem BSLambda.LLL.card_active_flag_through_ordered_pair (hT : IsDRTournamentWith Arc 7005 3502)
    {u v : ι} (huv : u ≠ v) (harc : Arc u v = true) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ u ∈ G.supp ∧ v ∈ G.supp).card ≤ 214620087510 := by sorry
