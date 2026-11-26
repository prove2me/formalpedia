-- Prove2me | Theorems.Thm_Auto_multilinear_interpolation_convexHull
-- name    : Auto.multilinear_interpolation_convexHull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:53:47.235123+00:00
-- url     : https://prove2.me/theorems/44e187dc-0206-4359-b78a-e0bf9691280d
-- title:
--   Auto: multilinear interpolation convex Hull
-- statement:
--   Multilinear complex interpolation over an arbitrary family of endpoint reciprocal vectors.
--   The conclusion holds at every point of their convex hull.  The endpoint constant is common to all
--   vertices, so every binary interpolation step preserves it exactly.  This is a SimpleFunc-level
--   theorem; the final `hzero` condition is the natural a.e.-zero compatibility needed for homogeneous
--   rescaling.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8257-L8367
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8257-L8367

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

theorem Auto.multilinear_interpolation_convexHull
    {m : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    (B : MultilinearMap ℂ (fun _ : Fin (m + 1) ↦ SimpleFunc X ℂ) (Y → ℂ))
    (q : ENNReal) (hq : 1 ≤ q) (A : ℝ) (hA : 0 < A)
    (hB_measurable : ∀ u : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (u i : X → ℂ) μ) → Measurable (B u))
    (hB_pair_integrable : ∀ (u : Fin (m + 1) → SimpleFunc X ℂ)
      (h : SimpleFunc Y ℂ),
      (∀ i, Integrable (u i : X → ℂ) μ) → Integrable (h : Y → ℂ) ν →
        Integrable (fun y ↦ B u y * h y) ν)
    (S : Set (Fin (m + 1) → ℝ))
    (hSbox : ∀ u ∈ S, ∀ i, 0 < u i ∧ u i ≤ 1)
    (hendpoint : ∀ u ∈ S, ∀ g : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (g i : X → ℂ) μ) →
        eLpNorm (B g) q ν ≤ ENNReal.ofReal A * ∏ i,
          eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ)
    (hzero : ∀ (u : Fin (m + 1) → ℝ), (∀ i, 0 < u i ∧ u i ≤ 1) →
      ∀ (g : Fin (m + 1) → SimpleFunc X ℂ) (i : Fin (m + 1)),
        eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ = 0 →
          eLpNorm (B g) q ν = 0)
    (u : Fin (m + 1) → ℝ) (hu : u ∈ convexHull ℝ S)
    (g : Fin (m + 1) → SimpleFunc X ℂ)
    (hg : ∀ i, Integrable (g i : X → ℂ) μ) :
    eLpNorm (B g) q ν ≤ ENNReal.ofReal A * ∏ i,
      eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ := by sorry
