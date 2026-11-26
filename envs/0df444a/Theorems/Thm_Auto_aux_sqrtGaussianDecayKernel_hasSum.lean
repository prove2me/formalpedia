-- Prove2me | Theorems.Thm_Auto_aux_sqrtGaussianDecayKernel_hasSum
-- name    : Auto.aux_sqrtGaussianDecayKernel_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:52:11.776614+00:00
-- url     : https://prove2.me/theorems/9d9e2a05-dfcb-44bb-b97e-6a2b120da653
-- title:
--   Auto: aux sqrt Gaussian Decay Kernel has Sum
-- statement:
--   This exports the positive Gaussian-mixture representation used in the proof of
--   `sqrtGaussianDecay`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5405-L5509
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L5405-L5509

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

theorem Auto.aux_sqrtGaussianDecayKernel_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => aux_sqrtGaussianCoefficient n *
      gaussianRescale (Real.sqrt (n + 1)) x)
      (aux_sqrtGaussianDecayKernel x) := by sorry
