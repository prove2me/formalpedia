-- Prove2me | Theorems.Thm_Auto_aux_gaussianRescale_complete_square
-- name    : Auto.aux_gaussianRescale_complete_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:53.626274+00:00
-- url     : https://prove2.me/theorems/f2206dfb-8df4-4012-aa54-c48608947fc8
-- title:
--   Auto: aux gaussian Rescale complete square
-- statement:
--   Auxiliary completed-square identity used to evaluate the convolution in
--   `gaussianRescale_convolution`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1370-L1399
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1370-L1399

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

theorem Auto.aux_gaussianRescale_complete_square (a μ x y : ℝ) (ha : 0 < a) (hμ : 0 < μ) :
    gaussianRescale a (x - y) * gaussianRescale μ y =
      (a⁻¹ * μ⁻¹ * Real.exp (-Real.pi * x ^ 2 / (a ^ 2 + μ ^ 2))) *
        Real.exp (-(Real.pi * (a ^ 2 + μ ^ 2) / (a ^ 2 * μ ^ 2)) *
          (y - μ ^ 2 / (a ^ 2 + μ ^ 2) * x) ^ 2) := by sorry
