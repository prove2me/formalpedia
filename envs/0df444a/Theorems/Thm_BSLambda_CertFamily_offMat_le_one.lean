-- Prove2me | Theorems.Thm_BSLambda_CertFamily_offMat_le_one
-- name    : BSLambda.CertFamily.offMat_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:15:55.501798+00:00
-- url     : https://prove2.me/theorems/7d6a06c5-c3e6-429d-9dd2-453d24552532
-- title:
--   Cert Family: off Mat le one
-- statement:
--   The entries of `R` are at most one, by `gram_le_one`; this is what turns the row and
--   column *counts* of Section 11.3 into bounds on the row and column *sums*.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L97-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L97-L101

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

theorem BSLambda.CertFamily.offMat_le_one (x y : Ones F.ind) : F.offMat x y ≤ 1 := by sorry
