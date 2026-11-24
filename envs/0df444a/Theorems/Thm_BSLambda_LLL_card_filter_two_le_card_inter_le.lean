-- Prove2me | Theorems.Thm_BSLambda_LLL_card_filter_two_le_card_inter_le
-- name    : BSLambda.LLL.card_filter_two_le_card_inter_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:03:54.104206+00:00
-- url     : https://prove2.me/theorems/ce11dd54-b5a3-4c9e-ac5c-15f8ad51402a
-- title:
--   LLL: card filter two le card inter le
-- statement:
--   Summing `card_filter_card_inter_eq` over the possible intersection sizes bounds the number
--   of `m`-element subsets meeting `V` in at least two vertices (Section 10.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L208-L233
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L208-L233

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

theorem BSLambda.LLL.card_filter_two_le_card_inter_le (V : Finset ι) {m : ℕ} (hvm : V.card ≤ m) :
    (Finset.univ.filter fun S : Finset ι => S.card = m ∧ 2 ≤ (V ∩ S).card).card
      ≤ ∑ s ∈ Finset.Icc 2 V.card,
          V.card.choose s * (Fintype.card ι - V.card).choose (m - s) := by sorry
