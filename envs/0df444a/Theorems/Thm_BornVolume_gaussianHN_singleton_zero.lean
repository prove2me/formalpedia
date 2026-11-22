-- Prove2me | Theorems.Thm_BornVolume_gaussianHN_singleton_zero
-- name    : BornVolume.gaussianHN_singleton_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:08.03048+00:00
-- url     : https://prove2.me/theorems/deab7c4d-dbd8-4686-8d70-7b1513eb04fd
-- title:
--   Born Volume: gaussian HN singleton zero
-- statement:
--   The origin is `gaussianHN`-null.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianCPN.lean#L214-L222
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianCPN.lean#L214-L222

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

theorem BornVolume.gaussianHN_singleton_zero [NeZero N] :
    gaussianHN {(0 : EuclideanSpace ℂ (Fin N))} = 0 := by sorry
