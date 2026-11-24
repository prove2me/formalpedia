-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_flagEvent_le
-- name    : BSLambda.LLL.pr_flagEvent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:44.366564+00:00
-- url     : https://prove2.me/theorems/596e82eb-34ac-4112-8c16-58fc5083266a
-- title:
--   LLL: pr flag Event le
-- statement:
--   **Section 8.1**: an active radius-one flag has probability `r ^ (-6)`.  After
--   conditioning on the owner gates, the six non-owner arc labels are independent and uniform,
--   and each is pinned to a single value.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L570-L576
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L570-L576

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

theorem BSLambda.LLL.pr_flagEvent_le [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {F : Flag1 ι} (hF : F.Active Arc) :
    pr (β := fun _ : ι × ι => Fin r) (flagEvent Arc F) ≤ 1 / (r : ℝ) ^ 6 := by sorry
