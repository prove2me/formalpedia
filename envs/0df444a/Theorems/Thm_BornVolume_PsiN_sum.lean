-- Prove2me | Theorems.Thm_BornVolume_PsiN_sum
-- name    : BornVolume.PsiN_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:54.802672+00:00
-- url     : https://prove2.me/theorems/661e8a13-2eed-4be3-866c-b503b46bf351
-- title:
--   Born Volume: Psi N sum
-- statement:
--   **Total-sum recovery.** `∑ i, Ψ_N(y) i = y last = S`. The inverse-map crux:
--   `(∑_k t_k)·S + (1−∑t)·S = S`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L312-L316
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L312-L316

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

theorem BornVolume.PsiN_sum (y : Fin (M + 1) → ℝ) : ∑ i, PsiN y i = y (Fin.last M) := by sorry
