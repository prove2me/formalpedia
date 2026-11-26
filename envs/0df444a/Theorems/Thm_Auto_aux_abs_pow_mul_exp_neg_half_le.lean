-- Prove2me | Theorems.Thm_Auto_aux_abs_pow_mul_exp_neg_half_le
-- name    : Auto.aux_abs_pow_mul_exp_neg_half_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:37.016431+00:00
-- url     : https://prove2.me/theorems/92d09f81-0ce5-597c-b973-448669976f9d
-- title:
--   Auto: aux abs pow mul exp neg half le
-- statement:
--   This auxiliary consequence of `aux_pow_mul_exp_neg_le` controls the monomial factor left
--   after splitting a Gaussian into two equal decaying exponentials.  It is used termwise in the
--   Hermite-polynomial proof of `gaussianBumpDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L91-L144
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L91-L144

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

theorem Auto.aux_abs_pow_mul_exp_neg_half_le (d : ℕ) (x : ℝ) :
    |x| ^ d * Real.exp (-(Real.pi / 2) * x ^ 2) ≤
      Real.rpow (((d + 1 : ℕ) : ℝ) * Real.exp (-1) / Real.pi) ((d : ℝ) / 2) := by sorry
