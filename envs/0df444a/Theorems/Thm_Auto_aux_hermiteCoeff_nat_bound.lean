-- Prove2me | Theorems.Thm_Auto_aux_hermiteCoeff_nat_bound
-- name    : Auto.aux_hermiteCoeff_nat_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:40.67856+00:00
-- url     : https://prove2.me/theorems/c78e6deb-b33a-45af-b5d1-eda6bfddc999
-- title:
--   Auto: aux hermite Coeff nat bound
-- statement:
--   This auxiliary estimate bounds the nonzero Hermite coefficient with index `d` in
--   the parametrization `2 * j + d`.  It is used termwise in the proof of
--   `gaussianBumpDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L271-L302
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L271-L302

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

theorem Auto.aux_hermiteCoeff_nat_bound (j d : ℕ) :
    Nat.doubleFactorial (2 * j - 1) * Nat.choose (2 * j + d) d ≤
      2 ^ (j + d) * (2 * j + d) ^ j := by sorry
