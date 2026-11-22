-- Prove2me | Theorems.Thm_BornVolume_hasFDerivAt_PsiN
-- name    : BornVolume.hasFDerivAt_PsiN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:23.169836+00:00
-- url     : https://prove2.me/theorems/688f531d-7da9-4cc6-96ba-f79f5ceefbef
-- title:
--   Born Volume: has FDeriv At Psi N
-- statement:
--   `Ψ_N` is Fréchet differentiable everywhere with derivative `psiFDerivN`. Proved
--   componentwise (`hasFDerivAt_pi`): each output coordinate is a product/affine
--   polynomial in the `y`-coordinates; the assembled derivative's matrix is `psiMat`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L209-L281
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L209-L281

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

theorem BornVolume.hasFDerivAt_PsiN (y : Fin (M + 1) → ℝ) : HasFDerivAt PsiN (psiFDerivN y) y := by sorry
