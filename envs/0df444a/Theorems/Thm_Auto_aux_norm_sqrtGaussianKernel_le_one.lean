-- Prove2me | Theorems.Thm_Auto_aux_norm_sqrtGaussianKernel_le_one
-- name    : Auto.aux_norm_sqrtGaussianKernel_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:05:32.711229+00:00
-- url     : https://prove2.me/theorems/b576a15b-8a4f-596e-86c7-29248788d32a
-- title:
--   Auto: aux norm sqrt Gaussian Kernel le one
-- statement:
--   This auxiliary bound is the zero-th order Fourier estimate for the square-root Gaussian
--   kernel. It supplies the uniform part of the later decay argument.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5528-L5546
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5528-L5546

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

theorem Auto.aux_norm_sqrtGaussianKernel_le_one (x : ℝ) :
    ‖aux_sqrtGaussianKernel x‖ ≤ 1 := by sorry
