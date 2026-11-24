-- Prove2me | Theorems.Thm_BSLambda_CertFamily_sensAt_le_c
-- name    : BSLambda.CertFamily.sensAt_le_c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:17:13.429659+00:00
-- url     : https://prove2.me/theorems/adeff7d4-4eed-4c71-84f0-6d410ca757db
-- title:
--   Cert Family: sens At le c
-- statement:
--   Only the `c` coordinates fixed by a containing certificate can be sensitive, so every
--   positive input has sensitivity at most `c` (Section 11.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L136-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L136-L139

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

theorem BSLambda.CertFamily.sensAt_le_c {i : ι} {x : Input V} (hx : (F.P i).Sat x) : sensAt F.ind x ≤ F.c := by sorry
