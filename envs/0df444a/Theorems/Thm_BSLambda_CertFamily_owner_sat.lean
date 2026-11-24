-- Prove2me | Theorems.Thm_BSLambda_CertFamily_owner_sat
-- name    : BSLambda.CertFamily.owner_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:14:21.157155+00:00
-- url     : https://prove2.me/theorems/a2e3e766-be68-4e76-88b0-f89ea2765ad1
-- title:
--   Cert Family: owner sat
-- statement:
--   The owner's certificate does contain the point.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L127-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L127-L128

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

theorem BSLambda.CertFamily.owner_sat (x : Ones F.ind) : (F.P (F.owner x)).Sat x.1 := by sorry
