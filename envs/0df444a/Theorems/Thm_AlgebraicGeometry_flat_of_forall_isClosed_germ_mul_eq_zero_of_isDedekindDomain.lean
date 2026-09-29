-- Prove2me | Theorems.Thm_AlgebraicGeometry_flat_of_forall_isClosed_germ_mul_eq_zero_of_isDedekindDomain
-- name    : AlgebraicGeometry.flat_of_forall_isClosed_germ_mul_eq_zero_of_isDedekindDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/95125195-02b4-59a4-b754-1d9ed48c310f
-- title:
--   Flatness over a Dedekind base tested at closed fibre points
-- statement:
--   Let $R$ be a Dedekind domain, let $X$ be a scheme and let $f : X \to \operatorname{Spec} R$ be a morphism of schemes that is locally of finite type. For a point $x \in X$, regard the stalk $\mathcal{O}_{X,x}$ as an $R$-module through the ring map obtained by composing the inverse of the canonical isomorphism $R \cong \Gamma(\operatorname{Spec} R, \mathcal{O})$ with the map $f^{\sharp}$ on global sections and then with the germ map $\Gamma(X, \mathcal{O}_X) \to \mathcal{O}_{X,x}$ at the top open. Assume: for every $x \in X$ such that the singleton $\{x\}$ is closed in $X$ and the prime ideal of $R$ corresponding to $f(x)$ is nonzero, the stalk $\mathcal{O}_{X,x}$ is torsion-free over $R$ in the sense that for all $c \in R$ with $c \neq 0$ and all $z \in \mathcal{O}_{X,x}$, the relation $c \cdot z = 0$ forces $z = 0$, the product being taken in $\mathcal{O}_{X,x}$ after transporting $c$ along the above map. The conclusion is that $f$ is a flat morphism.
--
--   This is the flatness criterion over a one-dimensional regular base in the form in which only the closed points of the fibres over the nonzero primes need be inspected: over a Dedekind domain flatness amounts to torsion-freeness, which is checked here at a restricted set of points. The proof goes through the criterion [`AlgebraicGeometry.flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain`](thm.html#AlgebraicGeometry.flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain), which expresses flatness as torsion-freeness of the sections over all affine opens, and the result is in turn used by [`AlgebraicGeometry.flat_of_forall_isClosed_natCast_mem_nonZeroDivisors_stalk`](thm.html#AlgebraicGeometry.flat_of_forall_isClosed_natCast_mem_nonZeroDivisors_stalk).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_flat_of_forall_isClosed_germ_mul_eq_zero_of_isDedekindDomain.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.flat_of_forall_isClosed_germ_mul_eq_zero_of_isDedekindDomain
    {R : Type u} [CommRing R] [IsDedekindDomain R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f]
    (h : ∀ x : X, IsClosed ({x} : Set X) → (f x).asIdeal ≠ ⊥ →
      ∀ (c : R) (z : X.presheaf.stalk x), c ≠ 0 →
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial) c * z = 0 → z = 0) :
    Flat f := by sorry
