-- Prove2me | Theorems.Thm_Auto_aux_sqrtGaussianDecayKernel_le_forty_bracket_sq
-- name    : Auto.aux_sqrtGaussianDecayKernel_le_forty_bracket_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:05:26.006861+00:00
-- url     : https://prove2.me/theorems/a0f443a7-1d7b-5298-8789-96eeebbc8334
-- title:
--   Auto: aux sqrt Gaussian Decay Kernel le forty bracket sq
-- statement:
--   This one-sided consequence of the absolute decay estimate is used for the upper bound in
--   `sqrtGaussianDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5381-L5383
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5381-L5383

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

theorem Auto.aux_sqrtGaussianDecayKernel_le_forty_bracket_sq (x : ℝ) :
    aux_sqrtGaussianDecayKernel x ≤ 40 * bracketBump x ^ 2 := by sorry
