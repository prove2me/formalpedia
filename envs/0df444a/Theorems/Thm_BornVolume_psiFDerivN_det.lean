-- Prove2me | Theorems.Thm_BornVolume_psiFDerivN_det
-- name    : BornVolume.psiFDerivN_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:03.572584+00:00
-- url     : https://prove2.me/theorems/5b91833e-51e9-4f48-867e-d3f24d7568ba
-- title:
--   Born Volume: psi FDeriv N det
-- statement:
--   **Jacobian determinant of `Ψ_N`.** `det (psiFDerivN y) = (y last)^M`. Immediate
--   from `psiMat_det` via `LinearMap.det_toLin'`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L201-L204
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L201-L204

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

theorem BornVolume.psiFDerivN_det (y : Fin (M + 1) → ℝ) :
    (psiFDerivN y).det = (y (Fin.last M)) ^ M := by sorry
