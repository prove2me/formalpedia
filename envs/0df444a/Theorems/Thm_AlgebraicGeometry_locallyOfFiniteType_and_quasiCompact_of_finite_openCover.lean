-- Prove2me | Theorems.Thm_AlgebraicGeometry_locallyOfFiniteType_and_quasiCompact_of_finite_openCover
-- name    : AlgebraicGeometry.locallyOfFiniteType_and_quasiCompact_of_finite_openCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/9be4adae-c336-511f-86b0-01f6ebb1832c
-- title:
--   Finite type and quasi-compactness from a finite cover by open immersions
-- statement:
--   Let $K$ be a commutative ring, and let $X$ and $J$ be schemes equipped with morphisms $f \colon X \to \operatorname{Spec} K$ and $\sigma \colon J \to \operatorname{Spec} K$ to the spectrum of $K$, where $f$ is assumed locally of finite type and quasi-compact. Suppose given a natural number $n$ and a family $\mathrm{cov} \colon \mathrm{Fin}\ n \to (X \to J)$ of morphisms such that each $\mathrm{cov}_i$ is an open immersion, each is a morphism over the base in the sense that $\mathrm{cov}_i$ followed by $\sigma$ equals $f$, and the images of the underlying continuous maps cover $J$, i.e. $\bigcup_{i} \operatorname{range}((\mathrm{cov}_i)_{\mathrm{base}}) = J$ as sets of points. The conclusion is the conjunction that $\sigma$ is locally of finite type and that $\sigma$ is quasi-compact. Note that all $n$ open immersions have the same source $X$; for $n = 0$ the covering hypothesis forces the underlying space of $J$ to be empty.
--
--   A descent statement of the standard kind: both properties of the structure morphism over an affine base are inherited by $J$ from $X$ along a finite cover of $J$ by open subschemes each isomorphic to $X$ over $\operatorname{Spec} K$. It is used in the construction of a Néron model by gluing charts, in [`ModularCurve.JZeroNeronObjectAtP.exists_neronGlue`](thm.html#ModularCurve.JZeroNeronObjectAtP.exists_neronGlue).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_locallyOfFiniteType_and_quasiCompact_of_finite_openCover.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u
open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.locallyOfFiniteType_and_quasiCompact_of_finite_openCover
    {K : Type u} [CommRing K] {X J : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of K)} {σ : J ⟶ Spec (CommRingCat.of K)}
    [LocallyOfFiniteType f] [QuasiCompact f]
    {n : ℕ} (cov : Fin n → (X ⟶ J)) (hoi : ∀ i, IsOpenImmersion (cov i))
    (cov_over : ∀ i, cov i ≫ σ = f) (hcov : ⋃ i, Set.range (cov i).base = Set.univ) :
    LocallyOfFiniteType σ ∧ QuasiCompact σ := by sorry
