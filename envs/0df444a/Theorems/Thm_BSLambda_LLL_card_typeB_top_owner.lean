-- Prove2me | Theorems.Thm_BSLambda_LLL_card_typeB_top_owner
-- name    : BSLambda.LLL.card_typeB_top_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:19.750225+00:00
-- url     : https://prove2.me/theorems/2767f978-41f7-4b4b-9539-7ad8a35495a8
-- title:
--   LLL: card type B top owner
-- statement:
--   **Section 8.2**, Type B, the fixed pair being the ordered top pair `(a, h) = (u, v)`: at
--   most `C(t,3)` such flags, with `t = 3502` in the construction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L466-L478
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L466-L478

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

theorem BSLambda.LLL.card_typeB_top_owner {d t : ℕ} (hT : IsDRTournamentWith Arc d t) {u v : ι} (huv : u ≠ v) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top = some u ∧ G.owner = v).card ≤ Nat.choose t 3 := by sorry
