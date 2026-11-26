-- Prove2me | Theorems.Thm_Auto_gaussianRescale_hasDerivAt
-- name    : Auto.gaussianRescale_hasDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:23.777148+00:00
-- url     : https://prove2.me/theorems/d739b879-2863-4a20-84ad-48533ee7fa5f
-- title:
--   Auto: gaussian Rescale has Deriv At
-- statement:
--   This auxiliary chain-rule formula transports the Gaussian derivative through rescaling.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L993-L1001
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L993-L1001

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

theorem Auto.gaussianRescale_hasDerivAt (t x : ℝ) :
    HasDerivAt (gaussianRescale t)
      (t⁻¹ * (-2 * Real.pi * (t⁻¹ * x) * gaussian (t⁻¹ * x)) * t⁻¹) x := by sorry
