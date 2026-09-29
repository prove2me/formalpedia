-- Prove2me | Theorems.Thm_AlgebraicGeometry_isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed
-- name    : AlgebraicGeometry.isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/3bce1398-007c-5963-9f6e-bc53550b2262
-- title:
--   Kummer coverings of normal integral schemes are finite étale
-- statement:
--   Let $R$ be a commutative ring, let $X$ be an integral scheme and let $f : X \to \operatorname{Spec} R$ be a morphism of schemes. Assume that every local ring $\mathcal{O}_{X,x}$ is integrally closed in its fraction field, let $k$ be a natural number whose image in $R$ is a unit, and let $g$ be a nonzero element of the function field $K(X)$ of $X$. Assume further that there are finitely many open subsets $U_0,\dots,U_{r-1}$ of $X$ covering $X$ (their supremum is $\top$) and nonzero elements $h_0,\dots,h_{r-1}$ of $K(X)$ such that for each index $a$ and each point $x \in U_a$ both $g/h_a^{\,k}$ and $h_a^{\,k}/g$ lie in the image of $\mathcal{O}_{X,x} \to K(X)$. Consider the composite of $\operatorname{Spec}$ of the structure map $K(X) \to K(X)[T]/(T^k - g)$, presented as `AdjoinRoot` of $X^k - C\,g$, with the canonical morphism $\operatorname{Spec} \mathcal{O}_{X,\eta} \to X$ at the generic point $\eta$ of $X$, and let $\pi$ be the induced morphism from the relative normalisation of this composite to $X$. Then $\pi$ is finite and étale.
--
--   This is the finite-étale half of the statement that a Kummer covering $T^k = g$ of a normal integral scheme, with $g$ locally a unit times a $k$-th power and $k$ invertible, has finite étale normalisation; it is used by [`AlgebraicGeometry.isFinite_and_etale_and_exists_section_fromNormalization_kummer_of_henselianLocalRing`](thm.html#AlgebraicGeometry.isFinite_and_etale_and_exists_section_fromNormalization_kummer_of_henselianLocalRing), where the remaining half produces a section over the closed fibre. The local input is the affine computation [`IsIntegrallyClosed.integralClosure_eq_adjoin_and_etale_and_finite_of_eq_mul_pow`](thm.html#IsIntegrallyClosed.integralClosure_eq_adjoin_and_etale_and_finite_of_eq_mul_pow), which identifies the integral closure of an integrally closed domain $B$ in $F[T]/(T^k-g)$, for $g = v h^k$ with $v \in B^\times$, as a monogenic étale finite $B$-algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

theorem AlgebraicGeometry.isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed
    {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of R))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (k : ℕ) (hk : IsUnit ((k : ℕ) : R))
    (g : X.functionField) (hg : g ≠ 0)
    (r : ℕ) (U : Fin r → X.Opens) (hU : (⨆ a, U a) = ⊤) (h : Fin r → X.functionField) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (x : X), x ∈ U a →
      g / h a ^ k ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ∧
      h a ^ k / g ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    let π := (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).fromNormalization
    IsFinite π ∧ AlgebraicGeometry.Etale π := by sorry
