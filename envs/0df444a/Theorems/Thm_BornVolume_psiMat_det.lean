-- Prove2me | Theorems.Thm_BornVolume_psiMat_det
-- name    : BornVolume.psiMat_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:53.957773+00:00
-- url     : https://prove2.me/theorems/685fa0b8-b091-443e-b051-ae4225d58743
-- title:
--   Born Volume: psi Mat det
-- statement:
--   **The Jacobian determinant is `S^M`.** Via the row operation "add every
--   `castSucc` row into the last row" (`det_updateRow_sum`, coefficient 1), after which
--   the matrix is two-block-triangular (last row zero off the corner) with diagonal
--   blocks `S·I_M` and `[1]`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L128-L179
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L128-L179

module
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Matrix.Block
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_LintegralFintypeProd
public import Definitions.Def_BornVolumeLean_Volume_MomentRatioUniformN
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Real Set
open scoped ENNReal
open BornVolume
variable {M : ℕ}

theorem BornVolume.psiMat_det (S : ℝ) (t : Fin M → ℝ) : (psiMat S t).det = S ^ M := by sorry
