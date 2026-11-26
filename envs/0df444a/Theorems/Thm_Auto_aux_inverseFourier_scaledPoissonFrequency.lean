-- Prove2me | Theorems.Thm_Auto_aux_inverseFourier_scaledPoissonFrequency
-- name    : Auto.aux_inverseFourier_scaledPoissonFrequency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:50:44.547804+00:00
-- url     : https://prove2.me/theorems/0b53017d-d275-4516-974f-44b467b96340
-- title:
--   Auto: aux inverse Fourier scaled Poisson Frequency
-- statement:
--   This evaluates the scaled Abel contribution used in the inverse-Fourier decomposition for
--   `sqrtGaussianDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4605-L4614
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4605-L4614

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

theorem Auto.aux_inverseFourier_scaledPoissonFrequency (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => (aux_scaledPoissonFrequency ξ : ℂ)) x =
      (aux_scaledPoissonKernel x : ℂ) := by sorry
