-- Prove2me | Theorems.Thm_AlgebraicGeometry_finrank_eq_natCard_sections_of_isFinite_of_isReduced_of_isAlgClosed
-- name    : AlgebraicGeometry.finrank_eq_natCard_sections_of_isFinite_of_isReduced_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/8928f344-cc12-5c9a-81ba-ba089cea640a
-- title:
--   Rank of a finite reduced k-scheme counts its k-points
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ be a scheme (both in the same universe), and let $f : X \to \operatorname{Spec} k$ be a morphism of schemes which is finite, with $X$ reduced. Let $s$ be a point of the one-point space $\operatorname{Spec} k$. The assertion is that the rank `f.finrank s` of the finite morphism $f$ at $s$ — the rank over the base at $s$ of the coherent sheaf $f_*\mathcal O_X$, which over the affine base $\operatorname{Spec} k$ is the dimension of $\Gamma(X,\mathcal O_X)$ as a $k$-vector space — is equal to `Nat.card` of the type of sections of $f$, namely of the subtype of those morphisms $x : \operatorname{Spec} k \to X$ for which $x$ followed by $f$ is the identity of $\operatorname{Spec} k$. Thus the $k$-dimension of the algebra of global sections of $X$ equals the number of $k$-points of $X$ over $\operatorname{Spec} k$ (with the convention that `Nat.card` is $0$ for an infinite type, a case excluded here by finiteness of $f$).
--
--   This is the scheme-theoretic form of the statement that a reduced finite algebra over an algebraically closed field is a finite product of copies of the field, so that its dimension counts its $k$-algebra homomorphisms to $k$; the proof reduces to the algebraic counterpart [`AlgHom.natCard_eq_finrank_of_isReduced_of_isAlgClosed`](thm.html#AlgHom.natCard_eq_finrank_of_isReduced_of_isAlgClosed). It is used to compute the ranks of finite schemes of level structures and extra levels on fake elliptic curves in the Čerednik–Drinfeld part of the development, and in the corresponding statement for finite étale morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_finrank_eq_natCard_sections_of_isFinite_of_isReduced_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.finrank_eq_natCard_sections_of_isFinite_of_isReduced_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsFinite f] [IsReduced X] (s : ↥(Spec (CommRingCat.of k))) :
    f.finrank s = Nat.card {x : Spec (CommRingCat.of k) ⟶ X // x ≫ f = 𝟙 (Spec (CommRingCat.of k))} := by sorry
