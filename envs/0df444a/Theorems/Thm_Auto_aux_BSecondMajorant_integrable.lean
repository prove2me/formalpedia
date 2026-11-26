-- Prove2me | Theorems.Thm_Auto_aux_BSecondMajorant_integrable
-- name    : Auto.aux_BSecondMajorant_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:01:17.144493+00:00
-- url     : https://prove2.me/theorems/489f71ba-f9d7-4e60-9505-79af4a174280
-- title:
--   Auto: aux BSecond Majorant integrable
-- statement:
--   This auxiliary theorem proves integrability of the explicit pointwise majorant for the
--   zero extension of $B''$, so that it can be used both for integrability and the stated norm
--   estimate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3899-L3925
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3899-L3925

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

theorem Auto.aux_BSecondMajorant_integrable :
    Integrable (fun x : ℝ =>
      144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun y : ℝ => y ^ 2 + 1 / 4) x +
        4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        12 * Real.exp (-(1 / 2) * x ^ 2) +
        8 * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.pi * aux_poissonFrequency x) := by sorry
