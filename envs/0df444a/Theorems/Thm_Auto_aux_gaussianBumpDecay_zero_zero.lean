-- Prove2me | Theorems.Thm_Auto_aux_gaussianBumpDecay_zero_zero
-- name    : Auto.aux_gaussianBumpDecay_zero_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:54:59.029954+00:00
-- url     : https://prove2.me/theorems/db80be0f-3b9a-457e-8f5b-a5a3085fe42f
-- title:
--   Auto: aux gaussian Bump Decay zero zero
-- statement:
--   This is the zero-th, zero-decay instance of the Gaussian bump estimate and is useful when
--   normalizing later Gaussian bounds.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L846-L851
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L846-L851

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

theorem Auto.aux_gaussianBumpDecay_zero_zero (x : ℝ) :
    |gaussian x| ≤ C_gaussianBumpDecay 0 0 * bracketBump x ^ 0 := by sorry
