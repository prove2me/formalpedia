-- Prove2me | Theorems.Thm_BSLambda_CertFamily_sat_unique
-- name    : BSLambda.CertFamily.sat_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:17:11.538015+00:00
-- url     : https://prove2.me/theorems/01fab2fc-ed3c-4491-8326-fa4c20b351a1
-- title:
--   Cert Family: sat unique
-- statement:
--   Distinct certificates are disjoint, so a point lies in at most one of them
--   (Section 4).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L118-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L118-L120

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

theorem BSLambda.CertFamily.sat_unique {i j : ι} {x : Input V} (hi : (F.P i).Sat x) (hj : (F.P j).Sat x) : i = j := by sorry
