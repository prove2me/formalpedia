-- Prove2me | Theorems.Thm_BSLambda_CertFamily_conflict_conflictCoord
-- name    : BSLambda.CertFamily.conflict_conflictCoord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:14:23.836122+00:00
-- url     : https://prove2.me/theorems/763a8026-300a-47f2-b5de-5da24b9c91e7
-- title:
--   Cert Family: conflict conflict Coord
-- statement:
--   The conflict coordinate does conflict.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L70-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L70-L71

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
open BSLambda.CertFamily
variable (F : CertFamily V ι)

theorem BSLambda.CertFamily.conflict_conflictCoord {i j : ι} (h : i ≠ j) : (F.P i).Conflict (F.P j) (F.conflictCoord h) := by sorry
