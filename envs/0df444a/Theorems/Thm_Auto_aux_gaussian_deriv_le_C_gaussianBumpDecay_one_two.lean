-- Prove2me | Theorems.Thm_Auto_aux_gaussian_deriv_le_C_gaussianBumpDecay_one_two
-- name    : Auto.aux_gaussian_deriv_le_C_gaussianBumpDecay_one_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:22.02641+00:00
-- url     : https://prove2.me/theorems/ffcc5d2c-b7d5-428f-a44e-bd2fa4768139
-- title:
--   Auto: aux gaussian deriv le C gaussian Bump Decay one two
-- statement:
--   This auxiliary estimate is the first-derivative, quadratic-decay Gaussian bound needed to
--   transport the manuscript's derivative estimate through a positive rescaling.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1007-L1047
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1007-L1047

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

theorem Auto.aux_gaussian_deriv_le_C_gaussianBumpDecay_one_two (x : ℝ) :
    |-2 * Real.pi * x * gaussian x| ≤
      C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 := by sorry
