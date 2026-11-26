-- Prove2me | Theorems.Thm_Auto_aux_wienerEnvelope_gaussian_le
-- name    : Auto.aux_wienerEnvelope_gaussian_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:23.51594+00:00
-- url     : https://prove2.me/theorems/c028b471-a89f-595c-b3fe-7bcb388663a4
-- title:
--   Auto: aux wiener Envelope gaussian le
-- statement:
--   This auxiliary envelope estimate supplies the integrable majorant needed to put the Gaussian
--   in the manuscript's Wiener space.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1086-L1106
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1086-L1106

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

theorem Auto.aux_wienerEnvelope_gaussian_le (x : ℝ) :
    wienerEnvelope gaussian 1 x ≤
      Real.exp Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) := by sorry
