-- Prove2me | Theorems.Thm_Auto_aux_integral_norm_auxiliaryFunctionB_le_six
-- name    : Auto.aux_integral_norm_auxiliaryFunctionB_le_six
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:45:54.913226+00:00
-- url     : https://prove2.me/theorems/69abb2f1-d08d-55b8-b8e3-15f10a9cf7b4
-- title:
--   Auto: aux integral norm auxiliary Function B le six
-- statement:
--   This auxiliary real-valued estimate extracts the sharpened $L^1$ bound for $B$ from the
--   corresponding `eLpNorm` clause of `auxiliaryFunctionB_properties`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4892-L4897
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4892-L4897

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

theorem Auto.aux_integral_norm_auxiliaryFunctionB_le_six :
    (∫ ξ : ℝ, ‖auxiliaryFunctionB ξ‖) ≤ 6 := by sorry
