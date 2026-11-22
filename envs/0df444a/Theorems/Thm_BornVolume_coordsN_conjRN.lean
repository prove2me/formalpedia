-- Prove2me | Theorems.Thm_BornVolume_coordsN_conjRN
-- name    : BornVolume.coordsN_conjRN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:34.926328+00:00
-- url     : https://prove2.me/theorems/cb7e7c23-1625-416e-9f53-411f1959eb0a
-- title:
--   Born Volume: coords N conj RN
-- statement:
--   `coordsN ∘ conjRN U = toEuclideanLin U.val ∘ coordsN`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianCPN.lean#L175-L179
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianCPN.lean#L175-L179

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

theorem BornVolume.coordsN_conjRN (U : Matrix.unitaryGroup (Fin N) ℂ)
    (y : EuclideanSpace ℝ (Fin N × Fin 2)) :
    coordsN (conjRN U y) = (Matrix.toEuclideanLin U.val) (coordsN y) := by sorry
