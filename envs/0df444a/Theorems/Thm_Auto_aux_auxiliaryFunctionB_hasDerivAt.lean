-- Prove2me | Theorems.Thm_Auto_aux_auxiliaryFunctionB_hasDerivAt
-- name    : Auto.aux_auxiliaryFunctionB_hasDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:44:05.025937+00:00
-- url     : https://prove2.me/theorems/c1f291ba-c711-5307-ab4d-55245ec34422
-- title:
--   Auto: aux auxiliary Function B has Deriv At
-- statement:
--   This auxiliary extension theorem upgrades the off-origin derivative formula for $B$ to the
--   continuous derivative extension at zero, which is needed for Fourier integration by parts.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2447-L2455
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2447-L2455

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

theorem Auto.aux_auxiliaryFunctionB_hasDerivAt (x : ℝ) :
    HasDerivAt auxiliaryFunctionB (auxiliaryFunctionBDerivative x) x := by sorry
