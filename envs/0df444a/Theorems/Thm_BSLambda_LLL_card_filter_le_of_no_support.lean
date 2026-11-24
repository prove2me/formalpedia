-- Prove2me | Theorems.Thm_BSLambda_LLL_card_filter_le_of_no_support
-- name    : BSLambda.LLL.card_filter_le_of_no_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:03:54.677801+00:00
-- url     : https://prove2.me/theorems/5fe4fd8f-5a71-4249-b720-5b0929f4514e
-- title:
--   LLL: card filter le of no support
-- statement:
--   The counting step behind both (L1) and (L2): if adjoining `h` to any `m + 1` indices
--   satisfying `P` gives a support on which `P` is impossible, then at most `m` indices other
--   than `h` satisfy `P`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L842-L850
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L842-L850

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

theorem BSLambda.LLL.card_filter_le_of_no_support {P : ι → Prop} [DecidablePred P] {h : ι} {m : ℕ}
    (hno : ∀ S : Finset ι, S.card = m + 2 → h ∈ S → (∀ i ∈ S, i ≠ h → P i) → False) :
    (Finset.univ.filter fun j => j ≠ h ∧ P j).card ≤ m := by sorry
