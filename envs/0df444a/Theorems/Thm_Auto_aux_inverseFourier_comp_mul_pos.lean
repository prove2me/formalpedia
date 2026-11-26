-- Prove2me | Theorems.Thm_Auto_aux_inverseFourier_comp_mul_pos
-- name    : Auto.aux_inverseFourier_comp_mul_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:56.799695+00:00
-- url     : https://prove2.me/theorems/92a6a005-bd0d-55f5-87ec-e18ee0699da5
-- title:
--   Auto: aux inverse Fourier comp mul pos
-- statement:
--   This change-of-variables identity is used by `aux_inverseFourier_scaledPoissonFrequency`
--   in the proof of Proposition `Auto.sqrtGaussianDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2091-L2104
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2091-L2104

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

theorem Auto.aux_inverseFourier_comp_mul_pos (f : ℝ → ℂ) (a x : ℝ) (ha : 0 < a) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => f (a * ξ)) x =
      (a⁻¹ : ℝ) • FourierTransformInv.fourierInv f (a⁻¹ * x) := by sorry
