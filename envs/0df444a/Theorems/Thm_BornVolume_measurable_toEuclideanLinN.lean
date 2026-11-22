-- Prove2me | Theorems.Thm_BornVolume_measurable_toEuclideanLinN
-- name    : BornVolume.measurable_toEuclideanLinN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:38.580865+00:00
-- url     : https://prove2.me/theorems/89781e41-e36f-4806-91b4-f8187e901978
-- title:
--   Born Volume: measurable to Euclidean Lin N
-- statement:
--   The `ℂ`-linear matrix action `toEuclideanLin U.val` is measurable.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianCPN.lean#L115-L117
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianCPN.lean#L115-L117

module
public import Definitions.Def_BornVolumeLean_Volume_GaussianFS
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_UnitaryTransitive
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Definitions.Def_BornVolumeLean_Volume_GaussianCPN
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
open BornVolume
variable {N : ℕ}

theorem BornVolume.measurable_toEuclideanLinN (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measurable (Matrix.toEuclideanLin U.val) := by sorry
