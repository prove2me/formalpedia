-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq
-- name    : AlgebraicCurve.exists_placeEquiv_ord_eq_and_ell_mapDomain_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/60f5b79b-a679-5547-bab2-5e59e1ec28f1
-- title:
--   Transport of places and divisors along F ≃_K F'
-- statement:
--   Let $K$ be a field, let $F$ and $F'$ be field extensions of $K$, and let $\sigma : F \to F'$ be an isomorphism of $K$-algebras. Here a place of $F/K$ is a valuation subring $\mathcal O_v \subseteq F$ which contains the image of $K$, is not all of $F$, and is a principal ideal ring; its degree $\deg v$ is the $K$-dimension of the residue field of $\mathcal O_v$, and $\operatorname{ord}_v(f)$ is the negative of the logarithm of the value of $f$ under the adic valuation attached to the height-one prime of $\mathcal O_v$. A divisor is a finitely supported function from places to $\mathbb Z$, its degree is $\sum_v D(v)\deg v$, it is principal when there is $f \neq 0$ in $F$ with $D(v) = \operatorname{ord}_v(f)$ for every $v$, and $\ell(D)$ is the $K$-dimension of the associated Riemann–Roch space. The assertion is that there exists a bijection $\pi$ from the places of $F/K$ to the places of $F'/K$ such that: the valuation subring of $\pi(v)$ is, as a subset of $F'$, the image under $\sigma$ of that of $v$; $\operatorname{ord}_{\pi(v)}(\sigma f) = \operatorname{ord}_v(f)$ for all $v$ and all $f \in F$; $\deg \pi(v) = \deg v$; and, for every divisor $D$ of $F/K$, the push-forward divisor $\pi_*D$ obtained by transporting the support along $\pi$ satisfies $\ell(\pi_*D) = \ell(D)$, $\deg(\pi_*D) = \deg D$, and $\pi_*D$ is principal if and only if $D$ is.
--
--   This is the transport of structure for the basic invariants of a one-variable function field along a $K$-isomorphism of the field itself: places, orders, residue degrees, Riemann–Roch dimensions, divisor degrees and principality all correspond. It is used to produce the induced map on divisor class groups, being cited in the construction [`AlgebraicCurve.CurveModel.exists_divisorClassMap`](thm.html#AlgebraicCurve.CurveModel.exists_divisorClassMap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open AlgebraicCurve

theorem AlgebraicCurve.exists_placeEquiv_ord_eq_and_ell_mapDomain_eq
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] {F' : Type w} [Field F'] [Algebra K F']
    (σ : F ≃ₐ[K] F') :
    ∃ π : Place K F ≃ Place K F',
      (∀ v : Place K F, ((π v).toValuationSubring : Set F') = σ '' (v.toValuationSubring : Set F)) ∧
      (∀ (v : Place K F) (f : F), (π v).ord (σ f) = v.ord f) ∧
      (∀ v : Place K F, (π v).deg = v.deg) ∧
      (∀ D : Divisor K F, ell (Finsupp.mapDomain π D) = ell D) ∧
      (∀ D : Divisor K F, Divisor.degree (Finsupp.mapDomain π D) = Divisor.degree D) ∧
      (∀ D : Divisor K F, Divisor.IsPrincipal (Finsupp.mapDomain π D) ↔ Divisor.IsPrincipal D) := by sorry
