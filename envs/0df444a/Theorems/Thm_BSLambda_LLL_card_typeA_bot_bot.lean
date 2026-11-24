-- Prove2me | Theorems.Thm_BSLambda_LLL_card_typeA_bot_bot
-- name    : BSLambda.LLL.card_typeA_bot_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:15.42881+00:00
-- url     : https://prove2.me/theorems/1020501f-1ff7-49c5-ae7c-b5eea809f183
-- title:
--   LLL: card type A bot bot
-- statement:
--   **Section 8.2**, Type A with an owner outside the fixed pair: at most
--   `t * C(d-2,2)` such flags, with `d = 7005`, `t = 3502` in the construction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L406-L427
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L406-L427

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

theorem BSLambda.LLL.card_typeA_bot_bot {d t : ℕ} (hT : IsDRTournamentWith Arc d t) {u v : ι} (huv : u ≠ v) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top = none ∧ u ∈ G.bot ∧ v ∈ G.bot).card
      ≤ t * Nat.choose (d - 2) 2 := by sorry
