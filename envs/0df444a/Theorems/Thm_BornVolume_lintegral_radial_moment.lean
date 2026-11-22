-- Prove2me | Theorems.Thm_BornVolume_lintegral_radial_moment
-- name    : BornVolume.lintegral_radial_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:50.538565+00:00
-- url     : https://prove2.me/theorems/eb69885c-99cb-4a71-8ed9-bae56c6b6d7f
-- title:
--   Born Volume: lintegral radial moment
-- statement:
--   **Radial moment.** `∫⁻_{S>0} Sⁿ·e^{−S/2} dS = 2^{n+1}·n!`.
--   The `n`-th moment of the `Exp(1/2)` shape; with `n = N−1` it is the normalisation
--   the post-substitution `S`-integral collapses to in the Gamma→Dirichlet change of
--   variables. Routes through `integral_rpow_mul_exp_neg_mul_Ioi` (`a = n+1`, `r = 1/2`,
--   giving `2^{n+1}·Γ(n+1)`) + `Real.Gamma_nat_eq_factorial` + the
--   `ofReal`↔`lintegral` bridge.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L42-L78
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean#L42-L78

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

theorem BornVolume.lintegral_radial_moment (n : ℕ) :
    ∫⁻ S in Ioi (0 : ℝ), ENNReal.ofReal (S ^ n * Real.exp (-S / 2))
      = ENNReal.ofReal ((2 : ℝ) ^ (n + 1) * (n.factorial : ℝ)) := by sorry
