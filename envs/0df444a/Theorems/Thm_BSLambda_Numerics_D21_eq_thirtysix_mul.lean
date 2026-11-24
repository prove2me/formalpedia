-- Prove2me | Theorems.Thm_BSLambda_Numerics_D21_eq_thirtysix_mul
-- name    : BSLambda.Numerics.D21_eq_thirtysix_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:26.807463+00:00
-- url     : https://prove2.me/theorems/41da1ea1-12f5-485c-bd54-003f4aa79a80
-- title:
--   Numerics: D21 eq thirtysix mul
-- statement:
--   `D₂₁ = 36 N₁`, with `N₁ = 214620087510` the radius-one flag count of Section 8.2
--   (`typeAFlagSum_eq` and `typeBFlagSum_eq`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L79-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L79-L79

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics

theorem BSLambda.Numerics.D21_eq_thirtysix_mul : D21 = 36 * 214620087510 := by sorry
