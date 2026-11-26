-- Prove2me | Theorems.Thm_Auto_aux_integral_norm_auxiliaryFunctionB_le_eight
-- name    : Auto.aux_integral_norm_auxiliaryFunctionB_le_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:51:18.330953+00:00
-- url     : https://prove2.me/theorems/021ac670-0e6d-55c1-a037-099a3e968d0d
-- title:
--   Auto: aux integral norm auxiliary Function B le eight
-- statement:
--   This weaker form of the $B$ integral estimate is retained for earlier auxiliary bounds.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4900-L4902
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4900-L4902

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

theorem Auto.aux_integral_norm_auxiliaryFunctionB_le_eight :
    (∫ ξ : ℝ, ‖auxiliaryFunctionB ξ‖) ≤ 8 := by sorry
