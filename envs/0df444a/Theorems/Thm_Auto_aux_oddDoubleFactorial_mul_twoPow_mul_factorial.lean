-- Prove2me | Theorems.Thm_Auto_aux_oddDoubleFactorial_mul_twoPow_mul_factorial
-- name    : Auto.aux_oddDoubleFactorial_mul_twoPow_mul_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:45.661898+00:00
-- url     : https://prove2.me/theorems/28455bb7-50b3-499d-8225-7425ae83c33e
-- title:
--   Auto: aux odd Double Factorial mul two Pow mul factorial
-- statement:
--   This auxiliary factorial identity rewrites the odd double factorial in the Hermite
--   coefficient formula.  It is used to retain the factor of `2` needed for the sharp
--   combinatorial estimate in `gaussianBumpDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L246-L264
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L246-L264

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

theorem Auto.aux_oddDoubleFactorial_mul_twoPow_mul_factorial (j : ℕ) :
    Nat.doubleFactorial (2 * j - 1) * (2 ^ j * j.factorial) = (2 * j).factorial := by sorry
