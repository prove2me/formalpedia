-- Prove2me | Theorems.Thm_Auto_aux_auxiliaryFunctionB_eq_fourierPoisson
-- name    : Auto.aux_auxiliaryFunctionB_eq_fourierPoisson
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:57:55.985844+00:00
-- url     : https://prove2.me/theorems/6ed2ccd8-90df-4921-bd13-2f701499c8db
-- title:
--   Auto: aux auxiliary Function B eq fourier Poisson
-- statement:
--   This auxiliary rewrite verifies that the concrete definition of $B$ uses precisely the
--   Fourier transform of the Poisson kernel appearing in the manuscript.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2190-L2198
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2190-L2198

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

theorem Auto.aux_auxiliaryFunctionB_eq_fourierPoisson (ξ : ℝ) :
    auxiliaryFunctionB ξ = 1 - sqrtOneMinusGaussian ξ -
      (FourierTransform.fourier (fun x : ℝ => (poissonKernel x : ℂ))
        (Real.sqrt Real.pi * ξ)).re := by sorry
