-- Prove2me | Theorems.Thm_BSLambda_CertFamily_offMat_nonneg
-- name    : BSLambda.CertFamily.offMat_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:18:51.579501+00:00
-- url     : https://prove2.me/theorems/4a2613b0-3632-49af-b127-2f20fe46630c
-- title:
--   Cert Family: off Mat nonneg
-- statement:
--   The entries of `R` are Gram entries or zero, hence nonnegative — one of the two
--   hypotheses of the Schur test (Section 11.3).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L84-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L84-L87

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)

theorem BSLambda.CertFamily.offMat_nonneg (x y : Ones F.ind) : 0 ≤ F.offMat x y := by sorry
