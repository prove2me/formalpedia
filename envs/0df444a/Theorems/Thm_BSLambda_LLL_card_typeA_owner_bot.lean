-- Prove2me | Theorems.Thm_BSLambda_LLL_card_typeA_owner_bot
-- name    : BSLambda.LLL.card_typeA_owner_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:08.936154+00:00
-- url     : https://prove2.me/theorems/e8529772-407a-476f-8a5e-26cfef116eac
-- title:
--   LLL: card type A owner bot
-- statement:
--   **Section 8.2**, Type A, the fixed pair being owner and bottom vertex: at most
--   `C(d-1,3)` such flags, specializing to `C(7004,3)` in the construction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L388-L401
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L388-L401

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

theorem BSLambda.LLL.card_typeA_owner_bot {d t : ℕ} (hT : IsDRTournamentWith Arc d t) {u v : ι} :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top = none ∧ G.owner = u ∧ v ∈ G.bot).card ≤ Nat.choose (d - 1) 3 := by sorry
