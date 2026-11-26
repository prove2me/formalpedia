-- Prove2me | Theorems.Thm_Auto_aux_norm_inverseFourier_auxiliaryFunctionBTrueSecondDerivative_le_fiftySix
-- name    : Auto.aux_norm_inverseFourier_auxiliaryFunctionBTrueSecondDerivative_le_fiftySix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:51:40.58981+00:00
-- url     : https://prove2.me/theorems/538c7a94-6654-4b89-9eaf-7c8dc927c5d8
-- title:
--   Auto: aux norm inverse Fourier auxiliary Function BTrue Second Derivative le fifty Six
-- statement:
--   This auxiliary uniform estimate is the zeroth-order inverse-Fourier bound for the true
--   second derivative of the continuous extension of $B'$.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4968-L4983
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4968-L4983

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

theorem Auto.aux_norm_inverseFourier_auxiliaryFunctionBTrueSecondDerivative_le_fiftySix (x : ℝ) :
    ‖FourierTransformInv.fourierInv
        (fun ξ : ℝ => (((if ξ = 0 then -Real.pi
          else auxiliaryFunctionBSecondDerivative ξ) : ℝ) : ℂ)) x‖ ≤ 56 := by sorry
