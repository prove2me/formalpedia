-- Prove2me | Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_hasDerivAt_zero
-- name    : Auto.aux_auxiliaryFunctionBDerivative_hasDerivAt_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:21.210795+00:00
-- url     : https://prove2.me/theorems/7e341207-fe16-516c-9143-ab70454d7a8d
-- title:
--   Auto: aux auxiliary Function BDerivative has Deriv At zero
-- statement:
--   This auxiliary derivative fact restores the genuine derivative at zero needed for Fourier
--   integration by parts.  Away from zero it is exactly the displayed formula for $B''$.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4327-L4338
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4327-L4338

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

theorem Auto.aux_auxiliaryFunctionBDerivative_hasDerivAt_zero :
    HasDerivAt auxiliaryFunctionBDerivative (-Real.pi) 0 := by sorry
