-- Prove2me | Theorems.Thm_Auto_aux_BSecondNumerator_bounds
-- name    : Auto.aux_BSecondNumerator_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:44:22.281804+00:00
-- url     : https://prove2.me/theorems/712c5ca4-13a5-422a-b8c5-ab956563583f
-- title:
--   Auto: aux BSecond Numerator bounds
-- statement:
--   This auxiliary Taylor-free estimate controls the numerator left after the cancellation in
--   the Gaussian quotient part of $B''$ on the only interval where its denominator is small.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2723-L2788
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2723-L2788

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

theorem Auto.aux_BSecondNumerator_bounds {x : ℝ} (hx : |x| ≤ 1 / 2) :
    0 ≤ aux_BSecondNumerator x ∧
      aux_BSecondNumerator x ≤ 2 * (Real.pi * x ^ 2) ^ 2 := by sorry
