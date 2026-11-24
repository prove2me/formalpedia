-- Prove2me | Theorems.Thm_BSLambda_LLL_card_typeB_bot_bot
-- name    : BSLambda.LLL.card_typeB_bot_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:26.854992+00:00
-- url     : https://prove2.me/theorems/a047877f-f9df-47a4-8bee-6c0c092637d0
-- title:
--   LLL: card type B bot bot
-- statement:
--   **Section 8.2**, Type B with both fixed vertices at the bottom: the top pair is one of the
--   `C(t,2)` arcs between the common in-neighbours of `u` and `v`, and the third bottom vertex is
--   one of `t - 2`, giving at most `C(t,2) * (t-2)` such flags.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L536-L568
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L536-L568

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

theorem BSLambda.LLL.card_typeB_bot_bot {d t : ℕ} (hT : IsDRTournamentWith Arc d t) {u v : ι} (huv : u ≠ v) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top ≠ none ∧ u ∈ G.bot ∧ v ∈ G.bot).card
      ≤ Nat.choose t 2 * (t - 2) := by sorry
