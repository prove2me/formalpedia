-- Prove2me | Theorems.Thm_Auto_aux_exp_three_half_pi_sq_le_four
-- name    : Auto.aux_exp_three_half_pi_sq_le_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:48:54.389183+00:00
-- url     : https://prove2.me/theorems/8beb741f-cb8b-4294-9892-1f0b3e958fb2
-- title:
--   Auto: aux exp three half pi sq le four
-- statement:
--   This auxiliary numerical estimate sharpens the local exponential factor in the
--   pass-5 proof of Proposition `Auto.auxiliaryFunctionB_properties`.  It
--   is used to obtain the stated
--   `56` bound for the $L^1$ norm of $B''$.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2824-L2843
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2824-L2843

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

theorem Auto.aux_exp_three_half_pi_sq_le_four {x : ℝ} (hx : |x| ≤ 1 / 2) :
    Real.exp (3 * (Real.pi * x ^ 2) / 2) ≤ 4 := by sorry
