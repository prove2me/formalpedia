-- Prove2me | Theorems.Thm_BornVolume_gaussianCPN_eq_fubiniStudy
-- name    : BornVolume.gaussianCPN_eq_fubiniStudy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:11.149091+00:00
-- url     : https://prove2.me/theorems/501a7dbe-c532-4a35-a296-93c43229f2b6
-- title:
--   Born Volume: gaussian CPN eq fubini Study
-- statement:
--   **The projectivised Gaussian equals the Fubini–Study measure on `ℂℙ^{N-1}`.**
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianCPN.lean#L247-L249
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/GaussianCPN.lean#L247-L249

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

theorem BornVolume.gaussianCPN_eq_fubiniStudy [NeZero N] (p₀ : CPN N) :
    gaussianCPN p₀ = fsMeasure p₀ := by sorry
