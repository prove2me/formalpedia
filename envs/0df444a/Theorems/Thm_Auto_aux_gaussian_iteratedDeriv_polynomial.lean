-- Prove2me | Theorems.Thm_Auto_aux_gaussian_iteratedDeriv_polynomial
-- name    : Auto.aux_gaussian_iteratedDeriv_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:26.906494+00:00
-- url     : https://prove2.me/theorems/f8573783-092b-51d2-961b-22f16958c1bf
-- title:
--   Auto: aux gaussian iterated Deriv polynomial
-- statement:
--   Auxiliary Hermite-type representation used by `gaussian_memSchwartz`, formalizing part (i)
--   of Proposition `Auto.gaussian_memSchwartz`.  It expresses each
--   derivative as a
--   polynomial times the Gaussian, which is needed to transfer rapid decay to all derivatives.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1123-L1143
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1123-L1143

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

theorem Auto.aux_gaussian_iteratedDeriv_polynomial : ∀ n : ℕ, ∃ p : Polynomial ℝ,
    ∀ x : ℝ, iteratedDeriv n gaussian x = p.eval x * gaussian x := by sorry
