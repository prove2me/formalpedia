-- Prove2me | Theorems.Thm_Auto_aux_wienerEnvelope_gaussianRescale_le
-- name    : Auto.aux_wienerEnvelope_gaussianRescale_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:34.760867+00:00
-- url     : https://prove2.me/theorems/46362006-1134-526d-9237-8f47258f8cec
-- title:
--   Auto: aux wiener Envelope gaussian Rescale le
-- statement:
--   This auxiliary envelope estimate transports the Gaussian Wiener bound to a positive
--   rescaling.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1259-L1303
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1259-L1303

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

theorem Auto.aux_wienerEnvelope_gaussianRescale_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    wienerEnvelope (gaussianRescale t) 1 x ≤
      t⁻¹ * Real.exp (Real.pi * t⁻¹ ^ 2) *
        Real.exp (-(Real.pi / 2) * (t⁻¹ * x) ^ 2) := by sorry
