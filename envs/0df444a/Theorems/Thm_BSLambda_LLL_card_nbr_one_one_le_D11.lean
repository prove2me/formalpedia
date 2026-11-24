-- Prove2me | Theorems.Thm_BSLambda_LLL_card_nbr_one_one_le_D11
-- name    : BSLambda.LLL.card_nbr_one_one_le_D11
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:32.308191+00:00
-- url     : https://prove2.me/theorems/5d4d2ecc-63b7-4525-b942-86f9316e6a8c
-- title:
--   LLL: card nbr one one le D11
-- statement:
--   A type-one event has at most `D11` type-one neighbours (Section 10.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L666-L685
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L666-L685

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

theorem BSLambda.LLL.card_nbr_one_one_le_D11 (hT : IsDRTournamentWith Arc 7005 3502)
    (F : {F : Flag1 ι // F.Active Arc}) :
    ((nbr (badSupp (Arc := Arc)) (Sum.inl F)).filter fun j => badTy j = false).card
      ≤ D11 := by sorry
