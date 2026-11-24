-- Prove2me | Theorems.Thm_BSLambda_CertFamily_owner_eq
-- name    : BSLambda.CertFamily.owner_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:22:25.076467+00:00
-- url     : https://prove2.me/theorems/11d5e94a-3539-452a-abf1-5dfd1d29e7e2
-- title:
--   Cert Family: owner eq
-- statement:
--   The owner is the only index whose certificate contains the point.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L131-L132
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L131-L132

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

theorem BSLambda.CertFamily.owner_eq {x : Ones F.ind} {i : ι} (h : (F.P i).Sat x.1) : F.owner x = i := by sorry
