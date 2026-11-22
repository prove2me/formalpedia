-- Prove2me | Theorems.Thm_BornVolume_psiMat_col_sum
-- name    : BornVolume.psiMat_col_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:58.724156+00:00
-- url     : https://prove2.me/theorems/8b2540c0-4321-4b3b-af7e-bf1fb66bdcbe
-- title:
--   Born Volume: psi Mat col sum
-- statement:
--   Column-sum of `psiMat`: every column sums (over all rows) to `[j = last]`.
--   On a `castSucc` column the diagonal `S` and the last-row `−S` cancel; on the last
--   column `∑t + (1−∑t) = 1`. This is the content of the row operation.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L109-L122
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L109-L122

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

theorem BornVolume.psiMat_col_sum (S : ℝ) (t : Fin M → ℝ) (j : Fin (M + 1)) :
    ∑ i, psiMat S t i j = if j = Fin.last M then (1 : ℝ) else 0 := by sorry
