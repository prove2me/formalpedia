-- Prove2me | Theorems.Thm_Auto_aux_BSecondSharpMajorant_integral_le_fiftySix
-- name    : Auto.aux_BSecondSharpMajorant_integral_le_fiftySix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:50.211959+00:00
-- url     : https://prove2.me/theorems/2ecc4a7e-bdbe-4bbd-8526-0748b355d6c0
-- title:
--   Auto: aux BSecond Sharp Majorant integral le fifty Six
-- statement:
--   Auxiliary for Proposition `Auto.auxiliaryFunctionB_properties`,
--    formalized by
--   `auxiliaryFunctionB_properties`: this integrates the pass-5 sharp $B''$ majorant and verifies
--   the constant $56$.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3826-L3892
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3826-L3892

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

theorem Auto.aux_BSecondSharpMajorant_integral_le_fiftySix :
    (∫ x : ℝ,
      26 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        2 * Real.pi * gaussian x + 12 * Real.pi ^ 2 * x ^ 2 * gaussian x +
          Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)) ≤ 56 := by sorry
