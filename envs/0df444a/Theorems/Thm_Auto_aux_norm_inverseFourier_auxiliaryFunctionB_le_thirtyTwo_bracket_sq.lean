-- Prove2me | Theorems.Thm_Auto_aux_norm_inverseFourier_auxiliaryFunctionB_le_thirtyTwo_bracket_sq
-- name    : Auto.aux_norm_inverseFourier_auxiliaryFunctionB_le_thirtyTwo_bracket_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:51:47.072027+00:00
-- url     : https://prove2.me/theorems/203247d6-142d-41e4-8f10-53bfef1d6982
-- title:
--   Auto: aux norm inverse Fourier auxiliary Function B le thirty Two bracket sq
-- statement:
--   This auxiliary decay estimate combines the uniform and quadratic bounds for the inverse
--   Fourier transform of $B$ into the bracket-bump majorant used in `sqrtGaussianDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5025-L5073
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5025-L5073

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

theorem Auto.aux_norm_inverseFourier_auxiliaryFunctionB_le_thirtyTwo_bracket_sq (x : ℝ) :
    ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ ≤
      32 * bracketBump x ^ 2 := by sorry
