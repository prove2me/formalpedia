-- Prove2me | Theorems.Thm_Auto_convexHull_subset_of_binary
-- name    : Auto.convexHull_subset_of_binary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:53:39.110945+00:00
-- url     : https://prove2.me/theorems/8b0187f6-506b-5f4a-b7a2-8500aec70de5
-- title:
--   Auto: convex Hull subset of binary
-- statement:
--   A set containing the endpoints and closed under binary convex combinations contains their
--   convex hull.  This is the induction principle used to pass from two-endpoint interpolation to a
--   finite family of endpoints.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8010-L8016
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L8010-L8016

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

theorem Auto.convexHull_subset_of_binary
    {E : Type*} [AddCommMonoid E] [Module ℝ E] {S G : Set E}
    (hS : S ⊆ G)
    (hbinary : ∀ x ∈ G, ∀ y ∈ G, ∀ a b : ℝ,
      0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ G) :
    convexHull ℝ S ⊆ G := by sorry
