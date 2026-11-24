-- Prove2me | Theorems.Thm_BSLambda_LLL_card_nbr_type_one_le
-- name    : BSLambda.LLL.card_nbr_type_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:03:49.432439+00:00
-- url     : https://prove2.me/theorems/873f7ca4-6fe6-45b2-b1c3-867746f5ea3b
-- title:
--   LLL: card nbr type one le
-- statement:
--   Every type-one neighbour of a bad event is an active flag whose support contains one of
--   the `C(|V|,2)` pairs of the event's vertex set `V` (Section 10.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L292-L318
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L292-L318

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

theorem BSLambda.LLL.card_nbr_type_one_le (i : BadIdx Arc) :
    ((nbr (badSupp (Arc := Arc)) i).filter fun j => badTy j = false).card
      ≤ ∑ p ∈ (badVerts i).powersetCard 2,
          (Finset.univ.filter fun G : Flag1 ι => G.Active Arc ∧ p ⊆ G.supp).card := by sorry
