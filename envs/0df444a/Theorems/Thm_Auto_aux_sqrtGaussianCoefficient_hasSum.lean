-- Prove2me | Theorems.Thm_Auto_aux_sqrtGaussianCoefficient_hasSum
-- name    : Auto.aux_sqrtGaussianCoefficient_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:50:37.114073+00:00
-- url     : https://prove2.me/theorems/182b127d-1637-44fa-9406-0918b3bf82a6
-- title:
--   Auto: aux sqrt Gaussian Coefficient has Sum
-- statement:
--   This auxiliary binomial-series identity expands the real square-root profile.  It is used
--   to represent the inverse Fourier kernel in `sqrtGaussianDecay` as a positive Gaussian mixture.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4463-L4482
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4463-L4482

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

theorem Auto.aux_sqrtGaussianCoefficient_hasSum (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    @HasSum ℝ ℕ Real.instAddCommGroup.toAddCommMonoid _
      (fun n : ℕ => aux_sqrtGaussianCoefficient n * t ^ (n + 1))
      (1 - Real.sqrt (1 - t)) (SummationFilter.unconditional ℕ) := by sorry
