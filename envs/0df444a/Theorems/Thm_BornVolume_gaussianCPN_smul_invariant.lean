-- Prove2me | Theorems.Thm_BornVolume_gaussianCPN_smul_invariant
-- name    : BornVolume.gaussianCPN_smul_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:04.660732+00:00
-- url     : https://prove2.me/theorems/b7c3a62d-ed15-4248-b097-e9b522ced12f
-- title:
--   Born Volume: gaussian CPN smul invariant
-- statement:
--   `gaussianCPN p₀` is `U(N)`-invariant.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianCPN.lean#L227-L244
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianCPN.lean#L227-L244

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

theorem BornVolume.gaussianCPN_smul_invariant [NeZero N] (p₀ : CPN N) (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map (fun p => U • p) (gaussianCPN p₀) = gaussianCPN p₀ := by sorry
