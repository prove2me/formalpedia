-- Prove2me | Theorems.Thm_BSLambda_nbrs_eq_image
-- name    : BSLambda.nbrs_eq_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:04:47.104328+00:00
-- url     : https://prove2.me/theorems/166bd64c-aa10-4f7f-bc78-3bd8127131f2
-- title:
--   BSLambda: nbrs eq image
-- statement:
--   The neighbours of `x` are exactly the one-coordinate flips at sensitive coordinates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L84-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L84-L93

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

theorem BSLambda.nbrs_eq_image (f : Input V → Bool) (x : Input V) :
    nbrs f x = (sensCoords f x).image fun v => flipSet x {v} := by sorry
