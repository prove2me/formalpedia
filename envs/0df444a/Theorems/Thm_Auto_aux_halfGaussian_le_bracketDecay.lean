-- Prove2me | Theorems.Thm_Auto_aux_halfGaussian_le_bracketDecay
-- name    : Auto.aux_halfGaussian_le_bracketDecay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:43.673632+00:00
-- url     : https://prove2.me/theorems/0bc27c2b-c1e4-436b-98f5-254ff2aba9ba
-- title:
--   Auto: aux half Gaussian le bracket Decay
-- statement:
--   This auxiliary estimate supplies the arbitrary polynomial-decay factor for the
--   half-Gaussian left after the Hermite derivative estimate.  It is used in
--   `gaussianBumpDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L151-L239
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L151-L239

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

theorem Auto.aux_halfGaussian_le_bracketDecay (x : ℝ) (n : ℕ) :
    Real.exp (-(Real.pi / 2) * x ^ 2) ≤
      (4 * ((n + 1 : ℕ) : ℝ)) ^ ((n : ℝ) / 2) * bracketBump x ^ n := by sorry
