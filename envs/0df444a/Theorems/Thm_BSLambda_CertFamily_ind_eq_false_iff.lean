-- Prove2me | Theorems.Thm_BSLambda_CertFamily_ind_eq_false_iff
-- name    : BSLambda.CertFamily.ind_eq_false_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:14:16.632136+00:00
-- url     : https://prove2.me/theorems/ea444cfa-a083-4871-9f49-668fa0cdeef2
-- title:
--   Cert Family: ind eq false iff
-- statement:
--   A point is negative exactly when no certificate subcube contains it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L92-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L92-L93

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

theorem BSLambda.CertFamily.ind_eq_false_iff {x : Input V} : F.ind x = false ↔ ∀ i, ¬ (F.P i).Sat x := by sorry
