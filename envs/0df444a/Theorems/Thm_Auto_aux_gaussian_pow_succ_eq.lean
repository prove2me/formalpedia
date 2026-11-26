-- Prove2me | Theorems.Thm_Auto_aux_gaussian_pow_succ_eq
-- name    : Auto.aux_gaussian_pow_succ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:50:38.596171+00:00
-- url     : https://prove2.me/theorems/7754408c-4f76-4f18-86a4-c9ec9b3a20c6
-- title:
--   Auto: aux gaussian pow succ eq
-- statement:
--   This auxiliary identity identifies each power in the binomial expansion with the Gaussian
--   at the corresponding square-root scale, used by the positive-mixture proof of
--   `sqrtGaussianDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4489-L4498
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4489-L4498

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

theorem Auto.aux_gaussian_pow_succ_eq (x : ℝ) (n : ℕ) :
    gaussian x ^ (n + 1) = gaussian (Real.sqrt (n + 1) * x) := by sorry
