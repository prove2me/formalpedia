-- Prove2me | Theorems.Thm_Auto_aux_sqrtOneMinusGaussian_div_abs_tendsto
-- name    : Auto.aux_sqrtOneMinusGaussian_div_abs_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:57.631916+00:00
-- url     : https://prove2.me/theorems/809ca009-80d8-533b-a996-cd426b847e3b
-- title:
--   Auto: aux sqrt One Minus Gaussian div abs tendsto
-- statement:
--   This auxiliary limit is the positive square-root form of the preceding quadratic
--   Gaussian quotient.  It makes the extension at the origin in the formula for $B'$ explicit.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1844-L1852
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1844-L1852

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

theorem Auto.aux_sqrtOneMinusGaussian_div_abs_tendsto :
    Tendsto (fun x : ℝ => sqrtOneMinusGaussian x / |x|)
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (𝓝 (Real.sqrt Real.pi)) := by sorry
