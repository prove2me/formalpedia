-- Prove2me | Theorems.Thm_BSLambda_LLL_card_nbr_type_two_le
-- name    : BSLambda.LLL.card_nbr_type_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:06.865987+00:00
-- url     : https://prove2.me/theorems/9c9982a5-61c4-40b3-b337-ea120118a931
-- title:
--   LLL: card nbr type two le
-- statement:
--   The type-two neighbours of a bad event are counted by the nine-element supports meeting
--   its vertex set in at least two vertices (Section 10.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L260-L265
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L260-L265

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

theorem BSLambda.LLL.card_nbr_type_two_le (i : BadIdx Arc) :
    ((nbr (badSupp (Arc := Arc)) i).filter fun j => badTy j = true).card
      ≤ (Finset.univ.filter fun S : Finset ι =>
          S.card = 9 ∧ 2 ≤ (badVerts i ∩ S).card).card := by sorry
