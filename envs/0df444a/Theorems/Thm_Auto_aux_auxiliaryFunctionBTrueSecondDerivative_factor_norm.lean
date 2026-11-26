-- Prove2me | Theorems.Thm_Auto_aux_auxiliaryFunctionBTrueSecondDerivative_factor_norm
-- name    : Auto.aux_auxiliaryFunctionBTrueSecondDerivative_factor_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:51:38.564797+00:00
-- url     : https://prove2.me/theorems/e0305bcf-7753-4b81-9bbe-c2951318b0d4
-- title:
--   Auto: aux auxiliary Function BTrue Second Derivative factor norm
-- statement:
--   This auxiliary identity combines the two inverse-Fourier integration-by-parts formulas into
--   the quadratic multiplier relation used for decay of the inverse transform of $B$.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4998-L5009
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4998-L5009

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

theorem Auto.aux_auxiliaryFunctionBTrueSecondDerivative_factor_norm (x : ℝ) :
    ‖FourierTransformInv.fourierInv
        (fun ξ : ℝ => (((if ξ = 0 then -Real.pi
          else auxiliaryFunctionBSecondDerivative ξ) : ℝ) : ℂ)) x‖ =
      (4 * Real.pi ^ 2 * x ^ 2) *
        ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ := by sorry
