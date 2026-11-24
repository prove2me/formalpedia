-- Prove2me | Theorems.Thm_BSLambda_Construction_card_le_bs
-- name    : BSLambda.Construction.card_le_bs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:15.344553+00:00
-- url     : https://prove2.me/theorems/61e1c70c-3de2-4b84-a93d-2af808054c28
-- title:
--   Construction: card le bs
-- statement:
--   **The block-sensitivity lower bound**: `bs f ≥ |ι|` (Section 5, `bs(f) ≥ k`).  The
--   blocks `B_i` are nonempty, pairwise disjoint and sensitive at the all-zero input.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/BlockSens.lean#L63-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/BlockSens.lean#L63-L67

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r}

theorem BSLambda.Construction.card_le_bs [Fintype ι] [DecidableEq ι] [NeZero r] :
    Fintype.card ι ≤ bs (ind Arc γ) := by sorry
