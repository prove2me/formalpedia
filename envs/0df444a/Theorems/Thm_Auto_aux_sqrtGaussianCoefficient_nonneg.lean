-- Prove2me | Theorems.Thm_Auto_aux_sqrtGaussianCoefficient_nonneg
-- name    : Auto.aux_sqrtGaussianCoefficient_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:45:35.879175+00:00
-- url     : https://prove2.me/theorems/4d36e1bf-01b7-4105-a06f-c1355c189c60
-- title:
--   Auto: aux sqrt Gaussian Coefficient nonneg
-- statement:
--   This auxiliary positivity fact makes the binomial Gaussian-mixture terms nonnegative in
--   the proof of Proposition `Auto.sqrtGaussianDecay`, formalized by
--   `sqrtGaussianDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4451-L4457
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4451-L4457

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

theorem Auto.aux_sqrtGaussianCoefficient_nonneg (n : ℕ) :
    0 ≤ aux_sqrtGaussianCoefficient n := by sorry
