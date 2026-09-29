-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_of_isFinite_of_finrank_closedPoint_eq_one
-- name    : AlgebraicGeometry.isIso_of_isFinite_of_finrank_closedPoint_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/ef506b93-2690-52bf-8246-b8d66b5a3ec9
-- title:
--   Finite of rank one over a field is an isomorphism
-- statement:
--   Let $K$ be a field (a type in the lowest universe) and let $Z$ be a scheme, likewise in the lowest universe. Let $p : Z \to \operatorname{Spec} K$ be a morphism of schemes, where $\operatorname{Spec} K$ is the spectrum of $K$ regarded as a commutative ring, and assume that $p$ is finite (`IsFinite p`). Assume further that the rank of $p$ in the sense of Mathlib's `Scheme.Hom.finrank`, evaluated at the closed point of $\operatorname{Spec} K$ — that is, the rank attached to $p$ over the unique point of the base, which for a finite morphism over a field is the $K$-dimension of $\Gamma(Z,\mathcal O_Z)$ — is equal to $1$. The conclusion is that $p$ is an isomorphism of schemes, i.e. `IsIso p` holds; equivalently $Z$ is, via $p$, identified with $\operatorname{Spec} K$ itself. Thus the hypothesis of rank one at the single point of the base already forces $p$ to be invertible; no separatedness, flatness or local freeness hypothesis is imposed beyond finiteness.
--
--   This is the standard fact that a finite scheme over a field whose coordinate algebra has dimension one over that field is the base itself; the excluded degenerate cases are the empty scheme (rank $0$) and non-reduced examples such as $\operatorname{Spec} K[\varepsilon]$ (rank $2$). It is used in the theory of abelian schemes developed for the modularity argument, where it converts the statement that a stabiliser (kernel) subscheme over a field has rank one into the assertion that that kernel is trivial, in [`GoodReductionJacobian.AbelianSchemePropertyBundle.kernelTrivial_of_eulerChar_sq_eq_one`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.kernelTrivial_of_eulerChar_sq_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_of_isFinite_of_finrank_closedPoint_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isFinite_of_finrank_closedPoint_eq_one
    (K : Type) [Field K] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of K)) [IsFinite p]
    (h : p.finrank (IsLocalRing.closedPoint K) = 1) :
    IsIso p := by sorry
