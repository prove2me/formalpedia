-- Prove2me | Theorems.Thm_BSLambda_LLL_card_nbr_one_two_le_D12
-- name    : BSLambda.LLL.card_nbr_one_two_le_D12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:43.884445+00:00
-- url     : https://prove2.me/theorems/33837043-f89f-48a3-a791-58fd12c69efb
-- title:
--   LLL: card nbr one two le D12
-- statement:
--   A type-one event has at most `D12` type-two neighbours (Section 10.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L688-L704
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L688-L704

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

theorem BSLambda.LLL.card_nbr_one_two_le_D12 (hk : Fintype.card ι = 14011)
    (F : {F : Flag1 ι // F.Active Arc}) :
    ((nbr (badSupp (Arc := Arc)) (Sum.inl F)).filter fun j => badTy j = true).card
      ≤ D12 := by sorry
