-- Prove2me | Theorems.Thm_Auto_aux_integral_indicator_localOne
-- name    : Auto.aux_integral_indicator_localOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:44:47.918732+00:00
-- url     : https://prove2.me/theorems/10869280-87b0-43ce-b153-9a0404fee675
-- title:
--   Auto: aux integral indicator local One
-- statement:
--   This auxiliary integral computes the measure of the compact interval in the local
--   majorant for $B''$.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3570-L3576
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3570-L3576

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

theorem Auto.aux_integral_indicator_localOne :
    (∫ x : ℝ, (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun _ : ℝ => (1 : ℝ)) x) = 1 := by sorry
