-- Prove2me | Theorems.Thm_BSLambda_comp_apply_topBits
-- name    : BSLambda.comp_apply_topBits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:04.320241+00:00
-- url     : https://prove2.me/theorems/a58a1235-f983-4aea-b9b1-aa301dcd315d
-- title:
--   BSLambda: comp apply top Bits
-- statement:
--   `comp f g` is `f` applied to the top bits.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L96-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L96-L97

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*}

theorem BSLambda.comp_apply_topBits (f : Input W → Bool) (g : Input V → Bool) (x : Input (W × V)) :
    comp f g x = f (topBits g x) := by sorry
