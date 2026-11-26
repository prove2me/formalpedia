-- Prove2me | Theorems.Thm_Auto_aux_deriv_auxiliaryFunctionB_complex_integrable
-- name    : Auto.aux_deriv_auxiliaryFunctionB_complex_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:50:55.469191+00:00
-- url     : https://prove2.me/theorems/aea67309-3590-5938-b067-f66b9df01283
-- title:
--   Auto: aux deriv auxiliary Function B complex integrable
-- statement:
--   This auxiliary integrability statement supplies the derivative hypothesis for the first
--   inverse-Fourier integration-by-parts step.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4836-L4840
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4836-L4840

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

theorem Auto.aux_deriv_auxiliaryFunctionB_complex_integrable :
    Integrable (deriv (fun y : ℝ => (auxiliaryFunctionB y : ℂ))) := by sorry
