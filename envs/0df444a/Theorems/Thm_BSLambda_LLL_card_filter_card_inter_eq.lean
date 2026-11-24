-- Prove2me | Theorems.Thm_BSLambda_LLL_card_filter_card_inter_eq
-- name    : BSLambda.LLL.card_filter_card_inter_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:10.195374+00:00
-- url     : https://prove2.me/theorems/e993a911-3deb-424d-b47e-f069d54e77ab
-- title:
--   LLL: card filter card inter eq
-- statement:
--   The `m`-element subsets of `ι` meeting a fixed `V` in exactly `s` vertices are counted by
--   choosing the `s` shared vertices inside `V` and the other `m - s` outside `V` (Section 10.1);
--   this is the `Finset`-level refinement of Vandermonde's identity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L160-L203
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L160-L203

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

theorem BSLambda.LLL.card_filter_card_inter_eq (V : Finset ι) {s m : ℕ} (hsm : s ≤ m) :
    (Finset.univ.filter fun S : Finset ι => S.card = m ∧ (V ∩ S).card = s).card
      = V.card.choose s * (Fintype.card ι - V.card).choose (m - s) := by sorry
