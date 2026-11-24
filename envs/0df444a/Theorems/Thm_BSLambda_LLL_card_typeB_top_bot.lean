-- Prove2me | Theorems.Thm_BSLambda_LLL_card_typeB_top_bot
-- name    : BSLambda.LLL.card_typeB_top_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:19.964333+00:00
-- url     : https://prove2.me/theorems/9144e3cf-78c9-407d-927b-c35ea165a41a
-- title:
--   LLL: card type B top bot
-- statement:
--   **Section 8.2**, Type B with `u` the upper top vertex and `v` a bottom vertex: at most
--   `t * C(t-1,2)` such flags, with `t = 3502` in the construction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L483-L502
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L483-L502

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

theorem BSLambda.LLL.card_typeB_top_bot {d t : ℕ} (hT : IsDRTournamentWith Arc d t)
    {u v : ι} (harc : Arc u v = true) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top = some u ∧ v ∈ G.bot).card ≤ t * Nat.choose (t - 1) 2 := by sorry
