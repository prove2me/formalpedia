-- Prove2me | Theorems.Thm_BornVolume_image_PsiN
-- name    : BornVolume.image_PsiN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:35.536346+00:00
-- url     : https://prove2.me/theorems/97cc0a68-9924-4849-b13e-8cf3fc6d6a88
-- title:
--   Born Volume: image Psi N
-- statement:
--   **The image of `Ψ_N` over the domain is the positive quadrant.**
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L338-L376
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L338-L376

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

theorem BornVolume.image_PsiN : PsiN '' (domainN : Set (Fin (M + 1) → ℝ)) = posQuadrant := by sorry
