-- Prove2me | Theorems.Thm_Auto_aux_exp_neg_abs_sqrt_pi_le_poissonFrequency
-- name    : Auto.aux_exp_neg_abs_sqrt_pi_le_poissonFrequency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:37:47.817401+00:00
-- url     : https://prove2.me/theorems/b8de4817-f352-5a06-832d-1d2bc7bbb7a8
-- title:
--   Auto: aux exp neg abs sqrt pi le poisson Frequency
-- statement:
--   This auxiliary estimate controls the Abel profile at the scale $\sqrt\pi$ by the
--   integrable unscaled Abel profile.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2156-L2166
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2156-L2166

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

theorem Auto.aux_exp_neg_abs_sqrt_pi_le_poissonFrequency (x : ℝ) :
    Real.exp (-|Real.sqrt Real.pi * x|) ≤ aux_poissonFrequency x := by sorry
