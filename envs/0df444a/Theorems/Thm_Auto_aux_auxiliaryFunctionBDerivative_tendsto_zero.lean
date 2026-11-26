-- Prove2me | Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_tendsto_zero
-- name    : Auto.aux_auxiliaryFunctionBDerivative_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:48:48.615674+00:00
-- url     : https://prove2.me/theorems/20c808d5-a835-4470-89db-b33fb2c7310b
-- title:
--   Auto: aux auxiliary Function BDerivative tendsto zero
-- statement:
--   This auxiliary deleted-neighborhood limit verifies that the displayed formula for $B'$ has
--   the continuous value zero at the origin.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2320-L2429
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2320-L2429

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

theorem Auto.aux_auxiliaryFunctionBDerivative_tendsto_zero :
    Tendsto auxiliaryFunctionBDerivative
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (𝓝 0) := by sorry
