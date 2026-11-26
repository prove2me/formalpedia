-- Prove2me | Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_continuousAt_of_ne_zero
-- name    : Auto.aux_auxiliaryFunctionBDerivative_continuousAt_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:48:35.814857+00:00
-- url     : https://prove2.me/theorems/a0d95b98-6f63-4f88-8e67-e4d2cc07c6ef
-- title:
--   Auto: aux auxiliary Function BDerivative continuous At of ne zero
-- statement:
--   This auxiliary continuity statement transfers the smooth off-origin derivative of $B$ to
--   the explicit formula used for its continuous extension.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2303-L2314
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2303-L2314

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

theorem Auto.aux_auxiliaryFunctionBDerivative_continuousAt_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt auxiliaryFunctionBDerivative x := by sorry
