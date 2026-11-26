-- Prove2me | Theorems.Thm_Auto_aux_polynomial_gaussian_bound
-- name    : Auto.aux_polynomial_gaussian_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:32.952245+00:00
-- url     : https://prove2.me/theorems/1ae018ce-4206-4b1e-a6f7-9920dc99be00
-- title:
--   Auto: aux polynomial gaussian bound
-- statement:
--   Auxiliary global bound used by `gaussian_memSchwartz`, formalizing part (i) of Proposition
--   `Auto.gaussian_memSchwartz`.  It turns rapid Gaussian decay into a
--   uniform bound after
--   multiplication by an arbitrary polynomial.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1165-L1177
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/Gaussians.lean#L1165-L1177

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

theorem Auto.aux_polynomial_gaussian_bound (p : Polynomial ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |x| ^ k * |p.eval x * gaussian x| ≤ C := by sorry
