-- Prove2me | Theorems.Thm_Auto_aux_sq_mul_gaussian_integrable
-- name    : Auto.aux_sq_mul_gaussian_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:14.489583+00:00
-- url     : https://prove2.me/theorems/c4d8a922-2303-53d3-9dbf-29d6696fa7a5
-- title:
--   Auto: aux sq mul gaussian integrable
-- statement:
--   Auxiliary for Proposition `Auto.auxiliaryFunctionB_properties`,
--    formalized by
--   `auxiliaryFunctionB_properties`: this supplies the integrability of the Gaussian second moment
--   needed for the sharp tail majorant.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3479-L3483
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L3479-L3483

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

theorem Auto.aux_sq_mul_gaussian_integrable :
    Integrable (fun x : ℝ => x ^ 2 * gaussian x) := by sorry
