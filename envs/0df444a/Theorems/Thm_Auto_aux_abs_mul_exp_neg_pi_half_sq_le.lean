-- Prove2me | Theorems.Thm_Auto_aux_abs_mul_exp_neg_pi_half_sq_le
-- name    : Auto.aux_abs_mul_exp_neg_pi_half_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:06.915393+00:00
-- url     : https://prove2.me/theorems/26f169cf-3a14-5cbc-9c2f-ffa9a5b011d2
-- title:
--   Auto: aux abs mul exp neg pi half sq le
-- statement:
--   This auxiliary elementary estimate replaces the linear Gaussian factor arising in the
--   off-origin $B''$ bound by a standard integrable Gaussian.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3131-L3147
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3131-L3147

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

theorem Auto.aux_abs_mul_exp_neg_pi_half_sq_le (x : ℝ) :
    |x| * Real.exp (-(Real.pi / 2) * x ^ 2) ≤
      Real.exp (-(1 / 2) * x ^ 2) := by sorry
