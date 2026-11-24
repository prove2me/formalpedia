-- Prove2me | Theorems.Thm_BSLambda_card_nbrs
-- name    : BSLambda.card_nbrs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:58:11.162854+00:00
-- url     : https://prove2.me/theorems/066c1ba0-e331-4022-a1a1-68d271d29033
-- title:
--   BSLambda: card nbrs
-- statement:
--   The degree of `x` in `G_f` is `s(f,x)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L96-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L96-L97

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Hermitian
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V]
variable [DecidableEq V]

theorem BSLambda.card_nbrs (f : Input V → Bool) (x : Input V) : (nbrs f x).card = sensAt f x := by sorry
