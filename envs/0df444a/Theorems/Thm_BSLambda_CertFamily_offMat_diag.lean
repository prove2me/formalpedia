-- Prove2me | Theorems.Thm_BSLambda_CertFamily_offMat_diag
-- name    : BSLambda.CertFamily.offMat_diag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:18:52.711059+00:00
-- url     : https://prove2.me/theorems/ff082edc-e60e-4dfa-911c-7e222cb6f038
-- title:
--   Cert Family: off Mat diag
-- statement:
--   The diagonal of `R` vanishes, since a point owns itself: this is what makes `D` in the
--   splitting `G = D + R + Rᵀ` carry the whole diagonal (Section 11.3).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L91-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L91-L93

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

theorem BSLambda.CertFamily.offMat_diag (x : Ones F.ind) : F.offMat x x = 0 := by sorry
