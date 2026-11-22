-- Prove2me | Theorems.Thm_BornVolume_unitary_norm_preserving
-- name    : BornVolume.unitary_norm_preserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:50.807924+00:00
-- url     : https://prove2.me/theorems/b59a6e58-601c-4e23-8a4d-93afa1871b21
-- title:
--   Born Volume: unitary norm preserving
-- statement:
--   A unitary matrix's `toEuclideanLin` action preserves the Euclidean norm
--   (`‖U v‖ = ‖v‖`), from `Uᴴ U = 1`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianFS.lean#L30-L54
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianFS.lean#L30-L54

module
public import Definitions.Def_BornVolumeLean_Volume_MomentMeasurable
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Definitions.Def_BornVolumeLean_Volume_GaussianFS
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
open BornVolume
variable {N : ℕ}

theorem BornVolume.unitary_norm_preserving (U : Matrix.unitaryGroup (Fin N) ℂ)
    (v : EuclideanSpace ℂ (Fin N)) :
    ‖(Matrix.toEuclideanLin U.val) v‖ = ‖v‖ := by sorry
