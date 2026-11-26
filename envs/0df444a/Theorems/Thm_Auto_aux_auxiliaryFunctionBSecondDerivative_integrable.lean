-- Prove2me | Theorems.Thm_Auto_aux_auxiliaryFunctionBSecondDerivative_integrable
-- name    : Auto.aux_auxiliaryFunctionBSecondDerivative_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:42:14.169829+00:00
-- url     : https://prove2.me/theorems/e2730258-dc9a-524c-96fd-a30916425389
-- title:
--   Auto: aux auxiliary Function BSecond Derivative integrable
-- statement:
--   This auxiliary integrability theorem turns the explicit majorant for the zero extension of
--   $B''$ into the integrability component of Proposition
--   `Auto.auxiliaryFunctionB_properties`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4369-L4373
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4369-L4373

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

theorem Auto.aux_auxiliaryFunctionBSecondDerivative_integrable :
    Integrable auxiliaryFunctionBSecondDerivative := by sorry
