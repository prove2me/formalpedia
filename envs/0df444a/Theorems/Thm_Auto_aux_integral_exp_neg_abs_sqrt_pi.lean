-- Prove2me | Theorems.Thm_Auto_aux_integral_exp_neg_abs_sqrt_pi
-- name    : Auto.aux_integral_exp_neg_abs_sqrt_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:38.175568+00:00
-- url     : https://prove2.me/theorems/b8f75b21-16da-4f43-b10e-99bd81b7dd49
-- title:
--   Auto: aux integral exp neg abs sqrt pi
-- statement:
--   Auxiliary for Proposition `Auto.auxiliaryFunctionB_properties`,
--    formalized by
--   `auxiliaryFunctionB_properties`: this evaluates the Abel tail occurring in the sharp $B''$
--   majorant.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3537-L3546
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3537-L3546

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

theorem Auto.aux_integral_exp_neg_abs_sqrt_pi :
    (∫ x : ℝ, Real.exp (-|Real.sqrt Real.pi * x|)) = 2 / Real.sqrt Real.pi := by sorry
