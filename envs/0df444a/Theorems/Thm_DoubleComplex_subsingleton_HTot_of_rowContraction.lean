-- Prove2me | Theorems.Thm_DoubleComplex_subsingleton_HTot_of_rowContraction
-- name    : DoubleComplex.subsingleton_HTot_of_rowContraction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/605bb422-3302-531b-b5bc-1230cdc52f2c
-- title:
--   Row contraction kills total cohomology of a bounded double complex
-- statement:
--   Let $R$ be a commutative ring and let $T$ be an object of the project's type [`DoubleComplex.Bounded R`](def/AlgebraicGeometry_DoubleComplex.html#L11): a family of $R$-modules $T.C\,p\,q$ indexed by pairs of natural numbers, together with $R$-linear horizontal maps $T.dH\,p\,q : T.C\,p\,q \to T.C\,(p+1)\,q$ and vertical maps $T.dV\,p\,q : T.C\,p\,q \to T.C\,p\,(q+1)$ satisfying $d_H^2 = 0$, $d_V^2 = 0$ and the commutation $d_V \circ d_H = d_H \circ d_V$, and with a bound $N$ such that $T.C\,p\,q$ is a subsingleton whenever $N \le p$ or $N \le q$. Suppose given $R$-linear maps $s\,p\,q : T.C\,(p+1)\,q \to T.C\,p\,q$ such that (i) $s\,0\,q\,(d_H x) = x$ for all $x \in T.C\,0\,q$, (ii) $s\,(p+1)\,q\,(d_H x) + d_H(s\,p\,q\,x) = x$ for all $x \in T.C\,(p+1)\,q$, and (iii) $s\,p\,(q+1)\,(d_V x) = d_V(s\,p\,q\,x)$ for all $x \in T.C\,(p+1)\,q$, i.e. the contraction commutes strictly with the vertical differential. Then for every $n$ the $R$-module [`DoubleComplex.HTot T n`](def/AlgebraicGeometry_DoubleComplex.html#L65), namely $\ker(\mathrm{dTot}\,T\,n)$ modulo the submodule which is $\bot$ for $n = 0$ and the preimage of the image of $\mathrm{dTot}\,T\,(n-1)$ for $n \ge 1$, is a subsingleton. Here $\mathrm{dTot}$ is the total differential assembled from $d_H$ and $(-1)^p d_V$ on the diagonal $p + q = n$. In particular for $n = 0$ the statement says that $\ker(\mathrm{dTot}\,T\,0)$ itself vanishes, and for $n \ge 1$ that every total cocycle is a total coboundary.
--
--   This is the standard acyclicity criterion for the total complex of a first-quadrant double complex whose rows are contractible by a contraction compatible with the vertical differential. It is used in the computation of the cohomology of tensor products of bounded cochain complexes, being cited by [`CochainCx.Bounded.finrank_HTot_tensor_eq_sum_mul`](thm.html#CochainCx.Bounded.finrank_HTot_tensor_eq_sum_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DoubleComplex_subsingleton_HTot_of_rowContraction.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem DoubleComplex.subsingleton_HTot_of_rowContraction
    {R : Type u} [CommRing R] (T : DoubleComplex.Bounded R)
    (s : ∀ p q : ℕ, T.C (p + 1) q →ₗ[R] T.C p q)
    (h0 : ∀ (q : ℕ) (x : T.C 0 q), s 0 q (T.dH 0 q x) = x)
    (hs : ∀ (p q : ℕ) (x : T.C (p + 1) q), s (p + 1) q (T.dH (p + 1) q x) + T.dH p q (s p q x) = x)
    (hsV : ∀ (p q : ℕ) (x : T.C (p + 1) q), s p (q + 1) (T.dV (p + 1) q x) = T.dV p q (s p q x))
    (n : ℕ) :
    Subsingleton (DoubleComplex.HTot T n) := by sorry
