-- Prove2me | Theorems.Thm_BSLambda_LLL_card_nbr_type_two_two_le
-- name    : BSLambda.LLL.card_nbr_type_two_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:02.921865+00:00
-- url     : https://prove2.me/theorems/80d9be8a-f762-4ed1-90a0-5a01ab38232b
-- title:
--   LLL: card nbr type two two le
-- statement:
--   Sharpened form of `card_nbr_type_two_le` for a type-two event: its own support is not one
--   of its neighbours, which is the `- 1` in `D22`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L269-L287
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L269-L287

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

theorem BSLambda.LLL.card_nbr_type_two_two_le (S : {S : Finset ι // S.card = 9}) :
    ((nbr (badSupp (Arc := Arc)) (Sum.inr S)).filter fun j => badTy j = true).card
      ≤ (Finset.univ.filter fun T : Finset ι =>
          T.card = 9 ∧ 2 ≤ (S.1 ∩ T).card).card - 1 := by sorry
