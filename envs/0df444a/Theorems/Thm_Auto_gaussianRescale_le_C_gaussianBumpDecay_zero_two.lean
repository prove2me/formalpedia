-- Prove2me | Theorems.Thm_Auto_gaussianRescale_le_C_gaussianBumpDecay_zero_two
-- name    : Auto.gaussianRescale_le_C_gaussianBumpDecay_zero_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:55:10.211886+00:00
-- url     : https://prove2.me/theorems/f14527c9-75a0-5670-a391-73a89e56ad55
-- title:
--   Auto: gaussian Rescale le C gaussian Bump Decay zero two
-- statement:
--   This rescaled zero-order bound is the instance of Gaussian decay used by the diagonal kernel.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L964-L979
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L964-L979

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

theorem Auto.gaussianRescale_le_C_gaussianBumpDecay_zero_two {t x : ℝ} (ht : 0 < t) :
    |gaussianRescale t x| ≤
      C_gaussianBumpDecay 0 2 * scaledBracketBump 2 t x := by sorry
