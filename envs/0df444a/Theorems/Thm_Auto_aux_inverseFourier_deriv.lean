-- Prove2me | Theorems.Thm_Auto_aux_inverseFourier_deriv
-- name    : Auto.aux_inverseFourier_deriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:45:35.805911+00:00
-- url     : https://prove2.me/theorems/ca048792-1734-46be-8aa8-3b015e4bc6e6
-- title:
--   Auto: aux inverse Fourier deriv
-- statement:
--   This auxiliary integration-by-parts identity transfers integrable derivative bounds to
--   inverse Fourier transforms in the normalization used in this formalization.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4782-L4790
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4782-L4790

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

theorem Auto.aux_inverseFourier_deriv {f : ℝ → ℂ}
    (hf : Integrable f) (h'f : Differentiable ℝ f) (hf' : Integrable (deriv f)) (x : ℝ) :
    FourierTransformInv.fourierInv (deriv f) x =
      (-(2 * Real.pi * Complex.I * x)) * FourierTransformInv.fourierInv f x := by sorry
