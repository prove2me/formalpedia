-- Prove2me | Theorems.Thm_Auto_aux_auxiliaryFunctionB_complex_hasDerivAt
-- name    : Auto.aux_auxiliaryFunctionB_complex_hasDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:45:34.725476+00:00
-- url     : https://prove2.me/theorems/f2a83965-b47c-53e3-bc62-1d7ef6f5f219
-- title:
--   Auto: aux auxiliary Function B complex has Deriv At
-- statement:
--   This auxiliary derivative formula complexifies the global differentiability of $B$ so that
--   the Fourier derivative theorem can be applied.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4796-L4799
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L4796-L4799

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

theorem Auto.aux_auxiliaryFunctionB_complex_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => (auxiliaryFunctionB y : ℂ))
      (auxiliaryFunctionBDerivative x) x := by sorry
