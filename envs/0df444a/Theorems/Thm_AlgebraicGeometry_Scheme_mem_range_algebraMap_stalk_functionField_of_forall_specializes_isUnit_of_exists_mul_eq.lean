-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_mem_range_algebraMap_stalk_functionField_of_forall_specializes_isUnit_of_exists_mul_eq
-- name    : AlgebraicGeometry.Scheme.mem_range_algebraMap_stalk_functionField_of_forall_specializes_isUnit_of_exists_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/1ad98335-1e6a-5cae-990f-a0a2c46988f3
-- title:
--   Prime-element criterion for regularity at a point of an integral scheme
-- statement:
--   Let $R$ be a commutative ring, $X$ an integral scheme, $c : X \to \operatorname{Spec} R$ a morphism of schemes, $r \in R$ and $x$ a point of $X$. Write $\varpi$ for the germ at $x$ of the global section $c^{\sharp}(r) \in \Gamma(X,\top)$ obtained by transporting $r$ through the isomorphism $\Gamma(\operatorname{Spec} R) \cong R$ and pulling back along $c$; thus $\varpi$ lies in the stalk $\mathcal{O}_{X,x}$. Assume that the principal ideal $(\varpi) \subseteq \mathcal{O}_{X,x}$ is prime and that $\varpi \neq 0$. Let $f$ be an element of the function field $K(X)$ of $X$, and assume: (i) there are $a, b \in \mathcal{O}_{X,x}$ with $b \notin (\varpi)$ and $f \cdot b = a$ in $K(X)$ (images under the canonical map $\mathcal{O}_{X,x} \to K(X)$); (ii) for every point $P$ of $X$ specialising to $x$ such that the germ of $c^{\sharp}(r)$ at $P$ is a unit in $\mathcal{O}_{X,P}$, $f$ lies in the image of $\mathcal{O}_{X,P} \to K(X)$. Then $f$ lies in the image of $\mathcal{O}_{X,x} \to K(X)$.
--
--   This is the scheme-theoretic form of the identity $S[1/\varpi] \cap S_{(\varpi)} = S$ for a prime element $\varpi$ of a domain $S$: a rational function with a denominator prime to $\varpi$ which is regular at every generisation of $x$ lying off the divisor $r = 0$ is regular at $x$ itself, with no normality, regularity or dimension hypothesis. It is used in the analysis of the cusp section on an integral model of a modular curve, where $r$ is a residue characteristic and the special fibre through $x$ is integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_mem_range_algebraMap_stalk_functionField_of_forall_specializes_isUnit_of_exists_mul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.mem_range_algebraMap_stalk_functionField_of_forall_specializes_isUnit_of_exists_mul_eq
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (CommRingCat.of R)) (r : R) (x : X)

    (hprime : (Ideal.span {(X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))}).IsPrime)
    (hne : (X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) ≠ 0)
    (f : X.functionField)

    (h1 : ∃ a b : X.presheaf.stalk x,
      b ∉ Ideal.span {(X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))} ∧
      f * algebraMap (X.presheaf.stalk x) X.functionField b = algebraMap (X.presheaf.stalk x) X.functionField a)

    (h2 : ∀ P : X, P ⤳ x →
      IsUnit ((X.presheaf.germ ⊤ P trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) →
      f ∈ Set.range (algebraMap (X.presheaf.stalk P) X.functionField)) :
    f ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by sorry
