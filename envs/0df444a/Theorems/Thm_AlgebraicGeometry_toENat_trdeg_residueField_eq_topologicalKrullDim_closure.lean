-- Prove2me | Theorems.Thm_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure
-- name    : AlgebraicGeometry.toENat_trdeg_residueField_eq_topologicalKrullDim_closure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/55a96175-21ad-5289-9c25-56ba81f78722
-- title:
--   Transcendence degree of a residue field equals dimx̄
-- statement:
--   Let $k$ be a field, let $X$ be a scheme, let $f : X \to \operatorname{Spec} k$ be a morphism of schemes which is locally of finite type, and let $x$ be a point of $X$. The residue field $\kappa(x) =$ `X.residueField x` is endowed with the $k$-algebra structure coming from the ring homomorphism obtained by composing the inverse of the canonical isomorphism $k \to \Gamma(\operatorname{Spec} k, \mathcal{O})$, the map $f^{\sharp}$ on global sections $\Gamma(\operatorname{Spec} k, \mathcal{O}) \to \Gamma(X, \mathcal{O}_X)$, the germ map $\Gamma(X,\mathcal{O}_X) \to \mathcal{O}_{X,x}$ at $x$, and the residue map $\mathcal{O}_{X,x} \to \kappa(x)$. With respect to this structure, the assertion is that the transcendence degree of $\kappa(x)$ over $k$, a cardinal, pushed forward to $\mathbb{N}_\infty$ by `Cardinal.toENat` and then included into $\mathbb{N}_\infty \cup \{\bot\}$, equals the topological Krull dimension of the closure of $\{x\}$ in $X$, taken with its subspace topology; here the topological Krull dimension is the supremum of lengths of chains of irreducible closed subsets, valued in $\mathbb{N}_\infty \cup \{\bot\}$ with $\bot$ for the empty space.
--
--   This is the standard dimension formula for schemes locally of finite type over a field, equating $\operatorname{trdeg}_k \kappa(x)$ with the dimension of the closed subscheme $\overline{\{x\}}$ (EGA IV, 5.2.1). It is used in the construction of valuation subrings of a function field attached to points whose local ring has Krull dimension one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.toENat_trdeg_residueField_eq_topologicalKrullDim_closure
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) =
      topologicalKrullDim ↥(closure ({x} : Set X)) := by sorry
