-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_intObstruction_owner_le
-- name    : BSLambda.LLL.pr_intObstruction_owner_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:48.743939+00:00
-- url     : https://prove2.me/theorems/5344f3ba-cf7a-4aee-a8e7-422375a34ba2
-- title:
--   LLL: pr int Obstruction owner le
-- statement:
--   **Section 9**: the radius-two obstruction for a fixed owner has probability at most
--   `radiusTwoConst / (9 * r ^ 20)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L1152-L1169
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L1152-L1169

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
open scoped Classical

theorem BSLambda.LLL.pr_intObstruction_owner_le [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9) {h : ι} (hh : h ∈ S) :
    pr (β := fun _ : ι × ι => Fin r)
        (Finset.univ.filter fun ω : GateCfg ι r => IntObstruction Arc 2 S h (toGamma ω))
      ≤ (radiusTwoOwnerConst : ℝ) / (r : ℝ) ^ 20 := by sorry
