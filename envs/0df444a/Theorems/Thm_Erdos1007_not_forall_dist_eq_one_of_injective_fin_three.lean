-- Prove2me | Theorems.Thm_Erdos1007_not_forall_dist_eq_one_of_injective_fin_three
-- name    : Erdos1007.not_forall_dist_eq_one_of_injective_fin_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:53:38.211825+00:00
-- url     : https://prove2.me/theorems/78e5ebdb-f18c-4059-949d-6298adcaffec
-- title:
--   Erdos1007: not forall dist eq one of injective fin three
-- statement:
--   In `ℝ³`, three pairwise distinct points cannot all lie at distance one from each of three
--   pairwise distinct centres. Equivalently, at most two points lie at distance one from three
--   distinct points.
--
--   Collinear centres make the perpendicular-bisector identities inconsistent. Non-collinear centres
--   force the common points onto a line orthogonal to their plane, and a line meets a unit sphere in
--   at most two points.
--
--   Blueprint node `lem:k33-dim`. Chaffee and Noble record the dimension statement as Lemma 3,
--   attributed there to Erdős, Harary and Tutte.
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/CompleteBipartiteLowerBound.lean#L196-L202
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/CompleteBipartiteLowerBound.lean#L196-L202

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Geometry.Euclidean.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_Erdos1007_Geometry_CompleteBipartiteLowerBound
set_option autoImplicit false
@[expose] public section
open Erdos1007
open Module Submodule AffineSubspace EuclideanGeometry
open scoped RealInnerProductSpace
public section

theorem Erdos1007.not_forall_dist_eq_one_of_injective_fin_three
    (a b : Fin 3 → EuclideanSpace ℝ (Fin 3)) (ha : Function.Injective a)
    (hb : Function.Injective b) (hdist : ∀ i j, dist (a i) (b j) = 1) : False := by sorry
