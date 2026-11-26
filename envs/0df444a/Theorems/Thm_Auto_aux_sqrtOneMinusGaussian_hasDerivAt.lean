-- Prove2me | Theorems.Thm_Auto_aux_sqrtOneMinusGaussian_hasDerivAt
-- name    : Auto.aux_sqrtOneMinusGaussian_hasDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:50:13.454417+00:00
-- url     : https://prove2.me/theorems/d553abb1-0600-4a1a-baf3-2603c436f4b9
-- title:
--   Auto: aux sqrt One Minus Gaussian has Deriv At
-- statement:
--   This auxiliary differentiability formula supplies the square-root denominator derivative
--   away from its removable singularity.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4058-L4066
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4058-L4066

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

theorem Auto.aux_sqrtOneMinusGaussian_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt sqrtOneMinusGaussian
      ((2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x)) x := by sorry
