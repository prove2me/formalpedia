-- Prove2me | Theorems.Thm_Auto_multilinear_interpolation_convexHull_Lp
-- name    : Auto.multilinear_interpolation_convexHull_Lp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:53:52.764167+00:00
-- url     : https://prove2.me/theorems/affeb3d4-5f25-52ac-9d7e-c539abc7a454
-- title:
--   Auto: multilinear interpolation convex Hull Lp
-- statement:
--   The finite-endpoint convex-hull interpolation theorem for an `L²`-valued complex
--   multilinear map on integrable simple functions.  It is the quotient-valued form of
--   `multilinear_interpolation_convexHull`; its only additional compatibility hypothesis says that
--   the map vanishes in `L²` when one input has zero seminorm.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9017-L9078
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9017-L9078

module
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Definitions.Def_LeanNct_Auto_MultilinearInterpolation
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto

theorem Auto.multilinear_interpolation_convexHull_Lp
    {m : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    (B : MultilinearMap ℂ (fun _ : Fin (m + 1) ↦ SimpleFunc X ℂ) (Lp ℂ 2 ν))
    (A : ℝ) (hA : 0 < A)
    (S : Set (Fin (m + 1) → ℝ))
    (hSbox : ∀ u ∈ S, ∀ i, 0 < u i ∧ u i ≤ 1)
    (hendpoint : ∀ u ∈ S, ∀ g : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (g i : X → ℂ) μ) →
        ‖B g‖ₑ ≤ ENNReal.ofReal A * ∏ i,
          eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ)
    (hzero : ∀ (u : Fin (m + 1) → ℝ), (∀ i, 0 < u i ∧ u i ≤ 1) →
      ∀ (g : Fin (m + 1) → SimpleFunc X ℂ) (i : Fin (m + 1)),
        eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ = 0 →
          ‖B g‖ₑ = 0)
    (u : Fin (m + 1) → ℝ) (hu : u ∈ convexHull ℝ S)
    (g : Fin (m + 1) → SimpleFunc X ℂ)
    (hg : ∀ i, Integrable (g i : X → ℂ) μ) :
    ‖B g‖ₑ ≤ ENNReal.ofReal A * ∏ i,
      eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ := by sorry
