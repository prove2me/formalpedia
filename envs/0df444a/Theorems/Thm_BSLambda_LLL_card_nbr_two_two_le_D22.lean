-- Prove2me | Theorems.Thm_BSLambda_LLL_card_nbr_two_two_le_D22
-- name    : BSLambda.LLL.card_nbr_two_two_le_D22
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:36.991798+00:00
-- url     : https://prove2.me/theorems/d19639eb-7f20-4cce-a477-36e571e303d7
-- title:
--   LLL: card nbr two two le D22
-- statement:
--   A type-two event has at most `D22` other type-two neighbours (Section 10.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L730-L747
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L730-L747

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

theorem BSLambda.LLL.card_nbr_two_two_le_D22 (hk : Fintype.card ι = 14011)
    (S : {S : Finset ι // S.card = 9}) :
    ((nbr (badSupp (Arc := Arc)) (Sum.inr S)).filter fun j => badTy j = true).card
      ≤ D22 := by sorry
