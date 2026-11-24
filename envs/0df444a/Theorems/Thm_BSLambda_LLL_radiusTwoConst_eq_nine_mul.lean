-- Prove2me | Theorems.Thm_BSLambda_LLL_radiusTwoConst_eq_nine_mul
-- name    : BSLambda.LLL.radiusTwoConst_eq_nine_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:17.299783+00:00
-- url     : https://prove2.me/theorems/6f200015-f784-4d9d-a905-208de087be49
-- title:
--   LLL: radius Two Const eq nine mul
-- statement:
--   `radiusTwoConst` has one `radiusTwoOwnerConst` for each of the nine possible owners.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L811-L813
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L811-L813

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

theorem BSLambda.LLL.radiusTwoConst_eq_nine_mul : radiusTwoConst = 9 * radiusTwoOwnerConst := by sorry
