-- Prove2me | Theorems.Thm_BornVolume_gaussianHN_map_unitary
-- name    : BornVolume.gaussianHN_map_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:39.292017+00:00
-- url     : https://prove2.me/theorems/aa0065b6-ffcb-441e-ba1b-f6dd12039300
-- title:
--   Born Volume: gaussian HN map unitary
-- statement:
--   `gaussianHN` is invariant under the unitary matrix action on `ℂ^N`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianCPN.lean#L182-L190
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianCPN.lean#L182-L190

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

theorem BornVolume.gaussianHN_map_unitary (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map (Matrix.toEuclideanLin U.val) gaussianHN = gaussianHN := by sorry
