-- Prove2me | Theorems.Thm_Auto_aux_auxiliaryFunctionBDerivative_eLpNorm_one_le
-- name    : Auto.aux_auxiliaryFunctionBDerivative_eLpNorm_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:48:41.412817+00:00
-- url     : https://prove2.me/theorems/35752200-038a-5cf8-8cff-5ab89223cdd1
-- title:
--   Auto: aux auxiliary Function BDerivative e Lp Norm one le
-- statement:
--   This auxiliary $L^1$ estimate supplies the $B'$ norm clause of
--   `auxiliaryFunctionB_properties`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2657-L2709
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L2657-L2709

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

theorem Auto.aux_auxiliaryFunctionBDerivative_eLpNorm_one_le :
    eLpNorm auxiliaryFunctionBDerivative 1 volume ≤ ENNReal.ofReal 12 := by sorry
