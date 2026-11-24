-- Prove2me | Theorems.Thm_BSLambda_LLL_card_typeB_owner_bot
-- name    : BSLambda.LLL.card_typeB_owner_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:27.264909+00:00
-- url     : https://prove2.me/theorems/e05c38b8-5c50-4b9d-9e3d-bcf8d15b1c49
-- title:
--   LLL: card type B owner bot
-- statement:
--   **Section 8.2**, Type B with `u` the owner and `v` a bottom vertex: at most
--   `t * C(t-1,2)` such flags, with `t = 3502` in the construction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L507-L530
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L507-L530

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

theorem BSLambda.LLL.card_typeB_owner_bot {d t : ℕ} (hT : IsDRTournamentWith Arc d t)
    {u v : ι} (huv : u ≠ v) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top ≠ none ∧ G.owner = u ∧ v ∈ G.bot).card
      ≤ t * Nat.choose (t - 1) 2 := by sorry
