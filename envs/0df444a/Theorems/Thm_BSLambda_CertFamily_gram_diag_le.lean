-- Prove2me | Theorems.Thm_BSLambda_CertFamily_gram_diag_le
-- name    : BSLambda.CertFamily.gram_diag_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:17:20.707271+00:00
-- url     : https://prove2.me/theorems/c24628dc-45c3-4887-9711-4cf621a66abf
-- title:
--   Cert Family: gram diag le
-- statement:
--   The diagonal of the positive-side Gram matrix is bounded by `c` (Section 11.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L142-L144
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertFamily.lean#L142-L144

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

theorem BSLambda.CertFamily.gram_diag_le (x : Ones F.ind) : gram F.ind x x ≤ (F.c : ℝ) := by sorry
