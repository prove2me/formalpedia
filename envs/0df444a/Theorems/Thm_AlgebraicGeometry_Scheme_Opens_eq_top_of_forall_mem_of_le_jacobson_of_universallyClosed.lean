-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Opens_eq_top_of_forall_mem_of_le_jacobson_of_universallyClosed
-- name    : AlgebraicGeometry.Scheme.Opens.eq_top_of_forall_mem_of_le_jacobson_of_universallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/96a6a3f2-26e8-5fed-9c7e-e9c7531a2c10
-- title:
--   Universally closed morphisms: open sets over V(I) exhaust X
-- statement:
--   Let $R$ be a commutative ring and let $I$ be an ideal of $R$ contained in the Jacobson radical of the zero ideal, i.e. $I \le \mathrm{Jac}(\bot)$, the intersection of all maximal ideals of $R$. Let $X$ be a scheme and let $f \colon X \to \operatorname{Spec} R$ be a morphism of schemes which is universally closed (`UniversallyClosed f`). Let $W$ be an open subscheme of $X$, i.e. an element of the lattice `X.Opens`, and suppose that every point $x$ of $X$ whose image prime $f(x) \in \operatorname{Spec} R$ contains $I$ — that is, $I \le (f(x))^{\mathrm{asIdeal}}$ — lies in $W$; equivalently, $W$ contains the set-theoretic preimage $f^{-1}(V(I))$. The conclusion is that $W = \top$, the whole of $X$, as an element of the lattice of opens of $X$.
--
--   This is the standard device underlying the formal-function and Nakayama-type arguments for proper (or merely universally closed) morphisms over a ring with large Jacobson radical, such as a local or an $I$-adically complete ring: an open neighbourhood of the fibre over the closed locus $V(I)$ is already all of $X$. It is used in the study of invertible modules on schemes over adic thickenings, where a local property established over $V(I)$ must be propagated to the total space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Opens_eq_top_of_forall_mem_of_le_jacobson_of_universallyClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Opens.eq_top_of_forall_mem_of_le_jacobson_of_universallyClosed
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (W : X.Opens) (hW : ∀ x : X, I ≤ (f.base x).asIdeal → x ∈ W) : W = ⊤ := by sorry
