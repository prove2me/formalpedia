-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isPullback_of_glue_cocycle
-- name    : AlgebraicGeometry.Scheme.exists_isOpenImmersion_isPullback_of_glue_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/3caf2fcf-974d-5174-859d-a4b694551b15
-- title:
--   Gluing copies of a scheme along an open by a cocycle
-- statement:
--   Let $S$, $X$, $U$ be schemes (in a fixed universe), $f : X \to S$ a morphism, and $j : U \to X$ an open immersion. Let $\iota$ be a type in the same universe and let $t$ assign to each pair $i,k \in \iota$ an isomorphism $t_{ik} : U \cong U$. Three hypotheses are imposed: each $t_{ik}$ is a morphism over $S$ for the structure map $j$ followed by $f$, i.e. $t_{ik}$ followed by $j$ followed by $f$ equals $j$ followed by $f$; $t_{ii}$ is the identity isomorphism of $U$ for every $i$; and $t_{ik}$ followed by $t_{kl}$ equals $t_{il}$ for all $i,k,l$. The conclusion asserts the existence of a scheme $N$, a morphism $g_N : N \to S$ and a family of morphisms $e_i : X \to N$ indexed by $\iota$ such that: each $e_i$ is an open immersion; $e_i$ followed by $g_N$ equals $f$ for every $i$; the union over $i$ of the ranges of the underlying continuous maps of the $e_i$ is all of the space of $N$; and for all $i \neq k$ the square with projections $j : U \to X$ and $t_{ik}$ followed by $j$, over the maps $e_i$ and $e_k$ into $N$, is cartesian.
--
--   This is the classical gluing construction for schemes, specialised to the shape in which many copies of a single $S$-scheme $X$ are glued along one fixed open subscheme $U \subseteq X$ by a cocycle of $S$-automorphisms of $U$; the output is packaged as exactly the data a consumer needs, namely open-immersion charts over $S$, joint surjectivity of the charts and cartesian overlap squares identifying the intersection of charts $i$ and $k$ with $U$ via $t_{ik}$. It is used in the construction of a glued model over a local base, in [`ModularCurve.JZeroNeronObjectAtP.exists_neronGlue`](thm.html#ModularCurve.JZeroNeronObjectAtP.exists_neronGlue).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isPullback_of_glue_cocycle.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_isOpenImmersion_isPullback_of_glue_cocycle
    {S X U : Scheme.{u}} (f : X ⟶ S) (j : U ⟶ X) [IsOpenImmersion j]
    {ι : Type u} (t : ι → ι → (U ≅ U))
    (ht_over : ∀ i k, (t i k).hom ≫ j ≫ f = j ≫ f)
    (ht_refl : ∀ i, t i i = Iso.refl U)
    (ht_trans : ∀ i k l, (t i k).hom ≫ (t k l).hom = (t i l).hom) :
    ∃ (N : Scheme.{u}) (gN : N ⟶ S) (e : ι → (X ⟶ N)),
      (∀ i, IsOpenImmersion (e i)) ∧
      (∀ i, e i ≫ gN = f) ∧
      (⋃ i, Set.range (e i).base) = Set.univ ∧
      (∀ i k, i ≠ k → IsPullback j ((t i k).hom ≫ j) (e i) (e k)) := by sorry
