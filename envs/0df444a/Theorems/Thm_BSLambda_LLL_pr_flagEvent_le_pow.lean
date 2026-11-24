-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_flagEvent_le_pow
-- name    : BSLambda.LLL.pr_flagEvent_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:40.333348+00:00
-- url     : https://prove2.me/theorems/96d2e253-efc1-4b93-b8b6-1641e572602f
-- title:
--   LLL: pr flag Event le pow
-- statement:
--   **Section 8.1**: the flag event pins one uniform label per internal arc, each to a
--   single value read off the owner gates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L544-L565
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L544-L565

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

theorem BSLambda.LLL.pr_flagEvent_le_pow [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {F : Flag1 ι} (hF : F.Active Arc) :
    pr (β := fun _ : ι × ι => Fin r) (flagEvent Arc F)
      ≤ ((1 : ℝ) / r) ^ (arcSet Arc F.nonOwners).card := by sorry
