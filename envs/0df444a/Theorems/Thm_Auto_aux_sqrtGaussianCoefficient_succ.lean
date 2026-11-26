-- Prove2me | Theorems.Thm_Auto_aux_sqrtGaussianCoefficient_succ
-- name    : Auto.aux_sqrtGaussianCoefficient_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:50:34.11283+00:00
-- url     : https://prove2.me/theorems/9e065e5b-d97d-4a63-8b5e-ad7d4311ada4
-- title:
--   Auto: aux sqrt Gaussian Coefficient succ
-- statement:
--   This auxiliary recurrence reduces the sign of the next binomial coefficient in
--   `aux_sqrtGaussianCoefficient` to the preceding coefficient.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4439-L4444
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4439-L4444

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

theorem Auto.aux_sqrtGaussianCoefficient_succ (n : ℕ) :
    aux_sqrtGaussianCoefficient (n + 1) =
      aux_sqrtGaussianCoefficient n * ((n : ℝ) + 1 / 2) / ((n : ℝ) + 2) := by sorry
