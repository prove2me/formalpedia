-- Prove2me | Theorems.Thm_Auto_aux_scaledPoissonKernel_le_three_halves_bracket_sq
-- name    : Auto.aux_scaledPoissonKernel_le_three_halves_bracket_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:21.215742+00:00
-- url     : https://prove2.me/theorems/bc552356-5618-41ca-b743-760742eb8790
-- title:
--   Auto: aux scaled Poisson Kernel le three halves bracket sq
-- statement:
--   Auxiliary for Proposition `Auto.sqrtGaussianDecay`, formalized by
--   `sqrtGaussianDecay`: this is the pass-5 bracket-bump bound for the scaled Abel kernel.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5242-L5294
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5242-L5294

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

theorem Auto.aux_scaledPoissonKernel_le_three_halves_bracket_sq (x : ℝ) :
    aux_scaledPoissonKernel x ≤ (3 / 2 : ℝ) * bracketBump x ^ 2 := by sorry
