-- Prove2me | Theorems.Thm_Auto_aux_pow_mul_exp_neg_le
-- name    : Auto.aux_pow_mul_exp_neg_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:30.70612+00:00
-- url     : https://prove2.me/theorems/1ced42d2-c7cd-4c36-b201-d038cf9d6696
-- title:
--   Auto: aux pow mul exp neg le
-- statement:
--   This auxiliary maximization estimate bounds a monomial times a decaying exponential.
--   It is used to control the terms in the explicit Hermite-polynomial formula for the
--   Gaussian derivatives.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L56-L84
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L56-L84

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

theorem Auto.aux_pow_mul_exp_neg_le (n : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    y ^ n * Real.exp (-y) ≤ ((n : ℝ) * Real.exp (-1)) ^ n := by sorry
