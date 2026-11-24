-- Prove2me | Theorems.Thm_BSLambda_CertFamily_lam_sq_le_sqrt
-- name    : BSLambda.CertFamily.lam_sq_le_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:23:51.432104+00:00
-- url     : https://prove2.me/theorems/c2417eb3-13fa-41a3-ab5d-dbd929e49aa3
-- title:
--   Cert Family: lam sq le sqrt
-- statement:
--   The Spectral Lemma with `offBound` unfolded and the subtraction taken in `ℝ` rather than
--   in `ℕ`, which is how Section 11.3 displays it. Nothing downstream needs this form — `lam_sq_le`
--   is the one the development uses — but it is the statement free of a truncated subtraction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L272-L276
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L272-L276

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

theorem BSLambda.CertFamily.lam_sq_le_sqrt (hc : 1 ≤ F.c) :
    lam F.ind ^ 2 ≤ (F.c : ℝ) + 2 * Real.sqrt (((F.c : ℝ) - 1) * F.A * F.B) := by sorry
