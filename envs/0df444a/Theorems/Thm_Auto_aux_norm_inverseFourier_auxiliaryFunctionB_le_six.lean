-- Prove2me | Theorems.Thm_Auto_aux_norm_inverseFourier_auxiliaryFunctionB_le_six
-- name    : Auto.aux_norm_inverseFourier_auxiliaryFunctionB_le_six
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:51:09.644871+00:00
-- url     : https://prove2.me/theorems/6583462f-6af6-4ceb-bd4d-8ff1c8370d6e
-- title:
--   Auto: aux norm inverse Fourier auxiliary Function B le six
-- statement:
--   This auxiliary uniform estimate is the sharpened zeroth-order inverse-Fourier bound for
--   $B$.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4908-L4919
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4908-L4919

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

theorem Auto.aux_norm_inverseFourier_auxiliaryFunctionB_le_six (x : ℝ) :
    ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ ≤ 6 := by sorry
