-- Prove2me | Theorems.Thm_Auto_aux_norm_inverseFourier_auxiliaryFunctionB_le_fifteen_bracket_sq
-- name    : Auto.aux_norm_inverseFourier_auxiliaryFunctionB_le_fifteen_bracket_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:51:46.798206+00:00
-- url     : https://prove2.me/theorems/4660ad2f-8610-5a6c-b4f1-c75493272453
-- title:
--   Auto: aux norm inverse Fourier auxiliary Function B le fifteen bracket sq
-- statement:
--   Auxiliary for Proposition `Auto.sqrtGaussianDecay`, formalized by
--   `sqrtGaussianDecay`: this combines the sharpened uniform and second-derivative bounds for the
--   inverse transform of $B$.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5080-L5132
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5080-L5132

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_Notation
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Definitions.Def_LeanNct_Auto_Preliminaries_Gaussians
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section

theorem Auto.aux_norm_inverseFourier_auxiliaryFunctionB_le_fifteen_bracket_sq (x : ℝ) :
    ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ ≤
      15 * bracketBump x ^ 2 := by sorry
