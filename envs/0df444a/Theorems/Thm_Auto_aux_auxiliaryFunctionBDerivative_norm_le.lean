-- Prove2me | Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_norm_le
-- name    : Auto.aux_auxiliaryFunctionBDerivative_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:44:21.258832+00:00
-- url     : https://prove2.me/theorems/b436d5b0-b73a-448c-9ea6-4bc80d373763
-- title:
--   Auto: aux auxiliary Function BDerivative norm le
-- statement:
--   This auxiliary pointwise bound supplies a single integrable majorant for the continuous
--   extension of $B'$.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2561-L2631
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2561-L2631

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

theorem Auto.aux_auxiliaryFunctionBDerivative_norm_le (x : ℝ) :
    ‖auxiliaryFunctionBDerivative x‖ ≤
      Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.sqrt Real.pi * aux_poissonFrequency x := by sorry
