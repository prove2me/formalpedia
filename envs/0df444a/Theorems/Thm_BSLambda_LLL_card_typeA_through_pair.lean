-- Prove2me | Theorems.Thm_BSLambda_LLL_card_typeA_through_pair
-- name    : BSLambda.LLL.card_typeA_through_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:12.187259+00:00
-- url     : https://prove2.me/theorems/5edabe44-0790-4fc2-858a-1e8012509c13
-- title:
--   LLL: card type A through pair
-- statement:
--   **Section 8.2**: at most `N_A = C(d-1,3) + t C(d-2,2) = 143,100,492,510` Type-A flags pass
--   through the ordered pair `u → v`.  The case `owner = v` is empty: it needs the reverse arc.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L432-L461
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L432-L461

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

theorem BSLambda.LLL.card_typeA_through_pair (hT : IsDRTournamentWith Arc 7005 3502)
    {u v : ι} (huv : u ≠ v) (harc : Arc u v = true) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top = none ∧ u ∈ G.supp ∧ v ∈ G.supp).card
      ≤ 143100492510 := by sorry
