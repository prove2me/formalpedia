-- Prove2me | Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_complex_hasDerivAt
-- name    : Auto.aux_auxiliaryFunctionBDerivative_complex_hasDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:45:51.017143+00:00
-- url     : https://prove2.me/theorems/1963a051-ee21-50c0-906e-d995507e6234
-- title:
--   Auto: aux auxiliary Function BDerivative complex has Deriv At
-- statement:
--   This auxiliary derivative formula complexifies the true derivative of the continuous
--   extension of $B'$ for the second integration-by-parts step.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4814-L4820
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4814-L4820

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

theorem Auto.aux_auxiliaryFunctionBDerivative_complex_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => (auxiliaryFunctionBDerivative y : ℂ))
      ((if x = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative x) : ℝ) x := by sorry
