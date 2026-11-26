-- Prove2me | Theorems.Thm_Auto_aux_quadratic_inverseFourier_auxiliaryFunctionB_bound
-- name    : Auto.aux_quadratic_inverseFourier_auxiliaryFunctionB_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:28.007388+00:00
-- url     : https://prove2.me/theorems/bb2233bc-a03b-5463-9da0-48b575a35925
-- title:
--   Auto: aux quadratic inverse Fourier auxiliary Function B bound
-- statement:
--   This auxiliary estimate is the quadratic inverse-Fourier decay bound for $B$ obtained from
--   its second derivative.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5015-L5019
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5015-L5019

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

theorem Auto.aux_quadratic_inverseFourier_auxiliaryFunctionB_bound (x : ℝ) :
    (4 * Real.pi ^ 2 * x ^ 2) *
        ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ ≤ 56 := by sorry
