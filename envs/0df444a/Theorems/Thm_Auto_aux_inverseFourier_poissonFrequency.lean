-- Prove2me | Theorems.Thm_Auto_aux_inverseFourier_poissonFrequency
-- name    : Auto.aux_inverseFourier_poissonFrequency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:44:04.750903+00:00
-- url     : https://prove2.me/theorems/1726738e-6646-41f4-9689-18206d86ac75
-- title:
--   Auto: aux inverse Fourier poisson Frequency
-- statement:
--   This auxiliary computation is the inverse-Fourier half of the Poisson-to-Abel identity.
--   It evaluates the two exponential half-line integrals before applying Fourier inversion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2003-L2085
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2003-L2085

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

theorem Auto.aux_inverseFourier_poissonFrequency (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => (aux_poissonFrequency ξ : ℂ)) x =
      (poissonKernel x : ℂ) := by sorry
