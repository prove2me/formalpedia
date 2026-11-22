-- Prove2me | Theorems.Thm_BornVolume_expHalf_eq_withDensity_dExp
-- name    : BornVolume.expHalf_eq_withDensity_dExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:44.175184+00:00
-- url     : https://prove2.me/theorems/ae53504d-307d-4da2-b1bd-83da3aa26bb3
-- title:
--   Born Volume: exp Half eq with Density d Exp
-- statement:
--   The Born Volume construction uses the exp Half eq with Density d Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L395-L395
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L395-L395

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

theorem BornVolume.expHalf_eq_withDensity_dExp : expHalf = volume.withDensity dExp := by sorry
