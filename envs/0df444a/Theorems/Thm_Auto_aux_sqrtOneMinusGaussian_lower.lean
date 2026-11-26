-- Prove2me | Theorems.Thm_Auto_aux_sqrtOneMinusGaussian_lower
-- name    : Auto.aux_sqrtOneMinusGaussian_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:38:03.150626+00:00
-- url     : https://prove2.me/theorems/3995115a-a56e-5279-8405-8f13931db9c0
-- title:
--   Auto: aux sqrt One Minus Gaussian lower
-- statement:
--   This auxiliary lower bound controls the square-root denominator in the formula for $B'$ by
--   a Gaussian factor.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2469-L2514
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2469-L2514

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

theorem Auto.aux_sqrtOneMinusGaussian_lower (x : ℝ) :
    Real.sqrt Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2) ≤
      sqrtOneMinusGaussian x := by sorry
