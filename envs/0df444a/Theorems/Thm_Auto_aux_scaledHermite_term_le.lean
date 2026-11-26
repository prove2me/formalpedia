-- Prove2me | Theorems.Thm_Auto_aux_scaledHermite_term_le
-- name    : Auto.aux_scaledHermite_term_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:55.757018+00:00
-- url     : https://prove2.me/theorems/64360682-c1c3-5410-b4e4-97b9cc0e0822
-- title:
--   Auto: aux scaled Hermite term le
-- statement:
--   This auxiliary estimate combines the scaled Hermite coefficient and monomial bounds into
--   the explicit order-dependent factor required by `gaussianBumpDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L445-L597
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L445-L597

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

theorem Auto.aux_scaledHermite_term_le (m j d : Nat) (hm : m = 2 * j + d) :
    (Real.sqrt (2 * Real.pi)) ^ m * ((2 : Real) ^ (j + d) * (m : Real) ^ j) *
        (Real.sqrt (2 * Real.pi)) ^ d *
        (((d + 1 : Nat) : Real) * Real.exp (-1) / Real.pi) ^ ((d : Real) / 2) ≤
      (19 * ((m + 1 : Nat) : Real)) ^ ((m : Real) / 2) := by sorry
