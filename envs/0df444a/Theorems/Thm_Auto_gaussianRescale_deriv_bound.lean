-- Prove2me | Theorems.Thm_Auto_gaussianRescale_deriv_bound
-- name    : Auto.gaussianRescale_deriv_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:55:14.795801+00:00
-- url     : https://prove2.me/theorems/841b4ceb-ff1c-52aa-9268-7dd6915b46a8
-- title:
--   Auto: gaussian Rescale deriv bound
-- statement:
--   This first-order rescaled estimate is a downstream instance of Gaussian bump decay.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1050-L1065
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1050-L1065

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

theorem Auto.gaussianRescale_deriv_bound {t x : ℝ} (ht : 0 < t) :
    |deriv (gaussianRescale t) x| ≤
      t⁻¹ * C_gaussianBumpDecay 1 2 * scaledBracketBump 2 t x := by sorry
