-- Prove2me | Theorems.Thm_Auto_aux_BSecondGaussianPart_abs_le_outer_sharp
-- name    : Auto.aux_BSecondGaussianPart_abs_le_outer_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:29.735568+00:00
-- url     : https://prove2.me/theorems/62af154d-23ec-59f0-8c78-fe0cde9052c3
-- title:
--   Auto: aux BSecond Gaussian Part abs le outer sharp
-- statement:
--   Auxiliary for Proposition `Auto.auxiliaryFunctionB_properties`,
--    formalized by
--   `auxiliaryFunctionB_properties`: this is the pass-5 tail envelope for the Gaussian quotient
--   terms of $B''$.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3393-L3471
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3393-L3471

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

theorem Auto.aux_BSecondGaussianPart_abs_le_outer_sharp {x : ℝ}
    (hx : 1 / 2 ≤ |x|) :
    |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)| ≤
      2 * Real.pi * gaussian x + 12 * Real.pi ^ 2 * x ^ 2 * gaussian x := by sorry
