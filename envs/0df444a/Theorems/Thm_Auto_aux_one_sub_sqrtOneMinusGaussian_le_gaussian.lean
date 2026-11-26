-- Prove2me | Theorems.Thm_Auto_aux_one_sub_sqrtOneMinusGaussian_le_gaussian
-- name    : Auto.aux_one_sub_sqrtOneMinusGaussian_le_gaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:40.148212+00:00
-- url     : https://prove2.me/theorems/b898278a-cf6f-4381-b1dd-72ca091fdca5
-- title:
--   Auto: aux one sub sqrt One Minus Gaussian le gaussian
-- statement:
--   This auxiliary inequality gives an integrable Gaussian majorant for the square-root
--   Gaussian frequency profile.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4572-L4579
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4572-L4579

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

theorem Auto.aux_one_sub_sqrtOneMinusGaussian_le_gaussian (x : ℝ) :
    1 - sqrtOneMinusGaussian x ≤ gaussian x := by sorry
