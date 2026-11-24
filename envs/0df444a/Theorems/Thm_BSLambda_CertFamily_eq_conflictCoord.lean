-- Prove2me | Theorems.Thm_BSLambda_CertFamily_eq_conflictCoord
-- name    : BSLambda.CertFamily.eq_conflictCoord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:14:56.952097+00:00
-- url     : https://prove2.me/theorems/eca23589-10d3-4e85-a56b-b77b6b6dd12e
-- title:
--   Cert Family: eq conflict Coord
-- statement:
--   The conflict coordinate is the only coordinate that conflicts.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L74-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L74-L76

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

theorem BSLambda.CertFamily.eq_conflictCoord {i j : ι} (h : i ≠ j) {v : V} (hv : (F.P i).Conflict (F.P j) v) :
    v = F.conflictCoord h := by sorry
