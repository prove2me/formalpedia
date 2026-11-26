-- Prove2me | Theorems.Thm_Auto_aux_one_sub_sqrtOneMinusGaussian_nonneg
-- name    : Auto.aux_one_sub_sqrtOneMinusGaussian_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:40.549123+00:00
-- url     : https://prove2.me/theorems/3d12c5ed-ba64-496b-a594-9051596a622a
-- title:
--   Auto: aux one sub sqrt One Minus Gaussian nonneg
-- statement:
--   This auxiliary inequality is the nonnegative branch condition for the frequency profile
--   in the square-root Gaussian kernel.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4559-L4566
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4559-L4566

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

theorem Auto.aux_one_sub_sqrtOneMinusGaussian_nonneg (x : ℝ) :
    0 ≤ 1 - sqrtOneMinusGaussian x := by sorry
