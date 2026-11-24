-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_Active_card_arcs
-- name    : BSLambda.LLL.Flag1.Active.card_arcs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:37.812094+00:00
-- url     : https://prove2.me/theorems/c22fc5a7-bc92-4578-a6ee-43765cd66b78
-- title:
--   Active: card arcs
-- statement:
--   An active flag has exactly six internal arcs among its four non-owners: `C(4, 2) = 6`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L473-L476
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L473-L476

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
omit [Fintype ι]

theorem BSLambda.LLL.Flag1.Active.card_arcs {F : Flag1 ι} {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    (hF : F.Active Arc) : (arcSet Arc F.nonOwners).card = 6 := by sorry
