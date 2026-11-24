-- Prove2me | Theorems.Thm_BSLambda_LLL_card_active_flag_through_pair
-- name    : BSLambda.LLL.card_active_flag_through_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:03:54.684801+00:00
-- url     : https://prove2.me/theorems/e3fac7a3-7b67-418e-900c-cff548f17afa
-- title:
--   LLL: card active flag through pair
-- statement:
--   **Section 8.2**: at most `N_1` active flags pass through any two-element vertex set.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L644-L661
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L644-L661

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

theorem BSLambda.LLL.card_active_flag_through_pair (hT : IsDRTournamentWith Arc 7005 3502)
    {p : Finset ι} (hp : p.card = 2) :
    (Finset.univ.filter fun G : Flag1 ι => G.Active Arc ∧ p ⊆ G.supp).card
      ≤ 214620087510 := by sorry
