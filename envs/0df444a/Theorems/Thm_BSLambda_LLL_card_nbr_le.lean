-- Prove2me | Theorems.Thm_BSLambda_LLL_card_nbr_le
-- name    : BSLambda.LLL.card_nbr_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:43.514152+00:00
-- url     : https://prove2.me/theorems/aa984d28-3eaa-4908-a5d4-42fa8860e6e7
-- title:
--   LLL: card nbr le
-- statement:
--   The dependency counts, packaged as required by `pr_avoid_pos_two_type`.  Double regularity
--   is what pins the number `N_1` of active flags through a pair (Section 8.2).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L751-L763
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L751-L763

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

theorem BSLambda.LLL.card_nbr_le (hk : Fintype.card ι = 14011) (hT : IsDRTournamentWith Arc 7005 3502)
    (i : BadIdx Arc) (t : Bool) :
    ((nbr (badSupp (Arc := Arc)) i).filter fun j => badTy j = t).card
      ≤ badD (badTy i) t := by sorry
