-- Prove2me | Theorems.Thm_Auto_aux_gaussian_iteratedDeriv_hermite
-- name    : Auto.aux_gaussian_iteratedDeriv_hermite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:40.772844+00:00
-- url     : https://prove2.me/theorems/cf1fd3a7-13a8-506f-aab8-a01567736861
-- title:
--   Auto: aux gaussian iterated Deriv hermite
-- statement:
--   This auxiliary identity expresses an iterated derivative of the manuscript's Gaussian
--   through the Hermite polynomial formula in mathlib.  It is used to reduce
--   `gaussianBumpDecay` to a finite coefficient estimate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L347-L369
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L347-L369

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

theorem Auto.aux_gaussian_iteratedDeriv_hermite (m : ℕ) (x : ℝ) :
    iteratedDeriv m gaussian x =
      (Real.sqrt (2 * Real.pi)) ^ m *
        ((-1 : ℝ) ^ m * (Polynomial.aeval (Real.sqrt (2 * Real.pi) * x)
          (Polynomial.hermite m)) *
          Real.exp (-((Real.sqrt (2 * Real.pi) * x) ^ 2 / 2))) := by sorry
