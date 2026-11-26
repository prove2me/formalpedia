-- Prove2me | Theorems.Thm_Auto_aux_sqrtGaussianKernel_eq_inverseFourier_auxiliaryFunctionB_add_scaledPoisson
-- name    : Auto.aux_sqrtGaussianKernel_eq_inverseFourier_auxiliaryFunctionB_add_scaledPoisson
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:25.970306+00:00
-- url     : https://prove2.me/theorems/58b43f2b-6cce-5be2-a7c7-cda275c90e91
-- title:
--   Auto: aux sqrt Gaussian Kernel eq inverse Fourier auxiliary Function B add scaled Poisson
-- statement:
--   This inverse-Fourier decomposition combines $B$ with the scaled Abel profile in the proof of
--   `sqrtGaussianDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4641-L4680
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4641-L4680

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

theorem Auto.aux_sqrtGaussianKernel_eq_inverseFourier_auxiliaryFunctionB_add_scaledPoisson
    (x : ℝ) :
    aux_sqrtGaussianKernel x =
      FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x +
        (aux_scaledPoissonKernel x : ℂ) := by sorry
