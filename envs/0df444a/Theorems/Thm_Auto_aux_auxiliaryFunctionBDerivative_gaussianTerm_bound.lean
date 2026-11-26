-- Prove2me | Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_gaussianTerm_bound
-- name    : Auto.aux_auxiliaryFunctionBDerivative_gaussianTerm_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:48:31.158889+00:00
-- url     : https://prove2.me/theorems/4972a03e-167e-5a61-892d-93b88890dd2b
-- title:
--   Auto: aux auxiliary Function BDerivative gaussian Term bound
-- statement:
--   This auxiliary quotient estimate turns the lower bound on the square-root denominator into
--   the Gaussian part of an integrable majorant for $B'$.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2520-L2555
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2520-L2555

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

theorem Auto.aux_auxiliaryFunctionBDerivative_gaussianTerm_bound {x : ℝ} (hx : x ≠ 0) :
    |(-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x)| ≤
      Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) := by sorry
