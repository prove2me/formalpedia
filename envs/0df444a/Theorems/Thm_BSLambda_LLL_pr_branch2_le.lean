-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_branch2_le
-- name    : BSLambda.LLL.pr_branch2_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:39.129235+00:00
-- url     : https://prove2.me/theorems/92239567-a028-48ef-9fc1-a7cbfdc8ae7a
-- title:
--   LLL: pr branch2 le
-- statement:
--   **Section 9**: in a fixed branch the `28 - |X|` remaining arc labels are independent and
--   uniform after conditioning on the owner gates, and each must hit a target set of size at
--   most two.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L1055-L1085
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L1055-L1085

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}

theorem BSLambda.LLL.pr_branch2_le [NeZero r] {Arc : ι → ι → Bool} {S : Finset ι} {h : ι}
    {L : Finset ι} (w : (j : ι) → j ∈ L → Fin r)
    {X : Finset (ι × ι)} (hX : X ⊆ arcSet Arc (S.erase h)) :
    pr (β := fun _ : ι × ι => Fin r) (branch2 Arc S h L w X)
      ≤ ((2 : ℝ) / r) ^ ((arcSet Arc (S.erase h)).card - X.card) := by sorry
