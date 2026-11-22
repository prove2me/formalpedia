-- Prove2me | Theorems.Thm_BornVolume_measurableSet_domainN
-- name    : BornVolume.measurableSet_domainN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:25.133464+00:00
-- url     : https://prove2.me/theorems/6b7efe8a-1b53-4291-b105-76eec0678cf0
-- title:
--   Born Volume: measurable Set domain N
-- statement:
--   The Born Volume construction uses the measurable Set domain N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L297-L304
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L297-L304

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

theorem BornVolume.measurableSet_domainN : MeasurableSet (domainN (M := M)) := by sorry
