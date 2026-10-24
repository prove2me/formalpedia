-- Prove2me | Theorems.Thm_DiazModulus_quadratic_ratio_wronskian_free
-- name    : DiazModulus.quadratic_ratio_wronskian_free
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:55.410092+00:00
-- url     : https://prove2.me/theorems/ab066b9b-530a-49cb-b006-dcfac08efd4f
-- title:
--   For a ratio h = p(u)/q(u) of degree 2, 1 and w = J(u)/q(u), with J the Wronskian, are linearly independent over Q̄(h)
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $p, q \in \overline{\mathbb{Q}}[X]$ be coprime with $\max(\deg p, \deg q) = 2$, let $J = p'q - pq'$ be their Wronskian, and put $h = p(u)/q(u)$ and $w = J(u)/q(u)$. If $A, B \in \overline{\mathbb{Q}}[X]$ satisfy $A(h) + B(h)\,w = 0$, then $A = 0$ and $B = 0$.
--
--   Clearing denominators, this says that $1$ and $w$ are linearly independent over the field $\overline{\mathbb{Q}}(h)$.
--
--   **Proof.** Coprimality and degree give $q \neq 0$, so $q(u) \neq 0$. Also $h \notin \overline{\mathbb{Q}}$: otherwise $p - hq$ is a polynomial over $\overline{\mathbb{Q}}$ vanishing at the transcendental $u$, so $p = hq$, coprimality makes $q$ a unit, and both have degree $0$; hence $h$ is transcendental. Evaluating the second identity of `DiazModulus.quadratic_pencil_wronskian_identities` at $u$ and dividing by $q(u)^2$ gives $w^2 = \Delta(h)$, with $\Delta = d_2X^2 + d_1X + d_0$ built from the coefficients of that identity. If $A(h) + B(h)w = 0$, then $A(h)^2 = B(h)^2\Delta(h)$, so $A^2 = B^2\Delta$ in $\overline{\mathbb{Q}}[X]$, $h$ being transcendental. If $B = 0$ this gives $A = 0$. Otherwise $B^2$ divides $A^2$, so $B$ divides $A$, and $\Delta = R^2$ with $R = r_1X + r_0$ of degree at most $1$. Comparing coefficients gives $d_1^2 - 4d_2d_0 = 0$; but $d_1^2 - 4d_2d_0 = 16\,\mathrm{Res}$, with $\mathrm{Res} = [20]^2 - [21][10]$, which `DiazModulus.quadratic_pencil_resultant_ne_zero` says is non-zero.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. Uses DiazModulus.quadratic_pencil_wronskian_identities and DiazModulus.quadratic_pencil_resultant_ne_zero. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem quadratic_ratio_wronskian_free (u : ℂ) (hu : u ∉ Qbar) (p q : (↥Qbar)[X])
    (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2) (A B : (↥Qbar)[X])
    (hAB : aeval (aeval u p / aeval u q) A + aeval (aeval u p / aeval u q) B *
        (aeval u (derivative p * q - p * derivative q) / aeval u q) = 0) :
    A = 0 ∧ B = 0 := by
  sorry

end DiazModulus
