-- Prove2me | Theorems.Thm_Auto_aux_integral_gaussian_second_moment
-- name    : Auto.aux_integral_gaussian_second_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:36.919537+00:00
-- url     : https://prove2.me/theorems/ffb08bf9-f629-58b9-84e3-5e0924e1b460
-- title:
--   Auto: aux integral gaussian second moment
-- statement:
--   Auxiliary for Proposition `Auto.auxiliaryFunctionB_properties`,
--    formalized by
--   `auxiliaryFunctionB_properties`: this evaluates the Gaussian second moment in the sharp
--   tail estimate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3491-L3529
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3491-L3529

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

theorem Auto.aux_integral_gaussian_second_moment :
    (∫ x : ℝ, x ^ 2 * gaussian x) = (2 * Real.pi)⁻¹ := by sorry
