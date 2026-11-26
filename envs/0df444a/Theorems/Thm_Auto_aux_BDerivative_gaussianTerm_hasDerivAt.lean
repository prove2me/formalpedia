-- Prove2me | Theorems.Thm_Auto_aux_BDerivative_gaussianTerm_hasDerivAt
-- name    : Auto.aux_BDerivative_gaussianTerm_hasDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:56.873943+00:00
-- url     : https://prove2.me/theorems/76606895-bb87-455f-919d-99ebf32a1e0e
-- title:
--   Auto: aux BDerivative gaussian Term has Deriv At
-- statement:
--   This auxiliary quotient-rule calculation differentiates the Gaussian part of the displayed
--   formula for $B'$ away from zero.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4072-L4107
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4072-L4107

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

theorem Auto.aux_BDerivative_gaussianTerm_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ =>
      (-2 * Real.pi * y * gaussian y) / (2 * sqrtOneMinusGaussian y))
      (((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)) x := by sorry
