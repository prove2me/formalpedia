-- Prove2me | Theorems.Thm_DoubleComplex_nonempty_HTot_equiv_of_levelwise_equiv
-- name    : DoubleComplex.nonempty_HTot_equiv_of_levelwise_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/b0034af7-c62e-5791-a09c-abb1c97be0b0
-- title:
--   Levelwise isomorphic bounded double complexes have isomorphic total cohomology
-- statement:
--   Let $R$ be a commutative ring and let $D$, $D'$ be bounded double complexes of $R$-modules in the sense of the project structure [`DoubleComplex.Bounded`](def/AlgebraicGeometry_DoubleComplex.html#L11): each consists of $R$-modules $C^{p,q}$ indexed by $p,q \in \mathbb{N}$, horizontal differentials $d_H \colon C^{p,q} \to C^{p+1,q}$ and vertical differentials $d_V \colon C^{p,q} \to C^{p,q+1}$ that are $R$-linear, square to zero and commute with one another, together with a bound $N$ such that $C^{p,q}$ is a subsingleton whenever $N \le p$ or $N \le q$. Assume given, for all $p,q$, an $R$-linear equivalence $e^{p,q} \colon D.C^{p,q} \simeq D'.C^{p,q}$ such that $e^{p+1,q}(d_H x) = d_H'(e^{p,q} x)$ and $e^{p,q+1}(d_V x) = d_V'(e^{p,q} x)$ for every $x \in D.C^{p,q}$. Then, for every $n \in \mathbb{N}$, the type of $R$-linear equivalences between $\mathrm{HTot}\, D\, n$ and $\mathrm{HTot}\, D'\, n$ is nonempty, where $\mathrm{HTot}\, D\, n$ is the quotient of $\ker(d_{\mathrm{Tot}}^n)$ by the submodule `HTotB` — namely $\bot$ for $n = 0$, and for $n = n'+1$ the preimage in $\ker(d_{\mathrm{Tot}}^{n})$ of the range of $d_{\mathrm{Tot}}^{n'}$ — with $d_{\mathrm{Tot}}^{n}$ the total differential assembled componentwise as $d_H + (-1)^p d_V$ on the diagonal of total degree $n$. The conclusion asserts existence of such an isomorphism rather than producing a designated one.
--
--   This is the invariance of total cohomology of a (first-quadrant, bounded) double complex under a levelwise isomorphism commuting with both differentials, in the elementary $\ker/\operatorname{im}$ formulation used throughout the project. It serves as a transport principle in the alternating Čech cohomology vanishing programme, and is cited by the comparison of the bi-Čech double complex of a strip decomposition with a tensor-type complex, by the subsingleton criterion for bi-Čech total cohomology, and by the product variant [`DoubleComplex.nonempty_HTot_equiv_prod_of_levelwise_equiv_prod`](thm.html#DoubleComplex.nonempty_HTot_equiv_prod_of_levelwise_equiv_prod).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DoubleComplex_nonempty_HTot_equiv_of_levelwise_equiv.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem DoubleComplex.nonempty_HTot_equiv_of_levelwise_equiv
    {R : Type u} [CommRing R] (D D' : DoubleComplex.Bounded R)
    (e : ∀ p q : ℕ, D.C p q ≃ₗ[R] D'.C p q)
    (hH : ∀ (p q : ℕ) (x : D.C p q), e (p + 1) q (D.dH p q x) = D'.dH p q (e p q x))
    (hV : ∀ (p q : ℕ) (x : D.C p q), e p (q + 1) (D.dV p q x) = D'.dV p q (e p q x))
    (n : ℕ) :
    Nonempty (DoubleComplex.HTot D n ≃ₗ[R] DoubleComplex.HTot D' n) := by sorry
