-- Prove2me | Theorems.Thm_DiazModulus_quadratic_pencil_wronskian_span
-- name    : DiazModulus.quadratic_pencil_wronskian_span
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:50.681985+00:00
-- url     : https://prove2.me/theorems/b117f552-73c4-49b8-9c3b-beb302620a80
-- title:
--   For a coprime pencil of degree 2 in characteristic zero, q, p and the Wronskian p′q − pq′ span the polynomials of degree at most 2
-- statement:
--   Let $K$ be a field of characteristic zero, let $p, q \in K[X]$ be coprime with $\max(\deg p, \deg q) = 2$, and let $J = p'q - pq'$ be their Wronskian. Then every $R \in K[X]$ of degree at most $2$ is $R = aq + bp + cJ$ for some $a, b, c \in K$.
--
--   Characteristic zero is needed: in characteristic $2$, $p = X^2$ and $q = 1$ give $J = 0$.
--
--   **Proof.** Write $p_i, q_i$ for the coefficients of $X^i$ and $[ij] = p_iq_j - p_jq_i$. By `DiazModulus.quadratic_pencil_wronskian_identities`, $J = [21]X^2 + 2[20]X + [10]$, so the matrix $M$ whose rows are the coefficient vectors of $q$, $p$ and $J$ in the basis $(1, X, X^2)$ has determinant $-2\,\mathrm{Res}$, with $\mathrm{Res} = [20]^2 - [21][10]$. By `DiazModulus.quadratic_pencil_resultant_ne_zero`, $\mathrm{Res} \neq 0$, and $2 \neq 0$ in characteristic zero, so $M$ is invertible. If $r$ is the coefficient vector of $R$, the vector $v = rM^{-1}$ satisfies $vM = r$, which says, coefficient by coefficient, that $R = v_0q + v_1p + v_2J$; the coefficients of degree at least $3$ vanish on both sides.
--
--   **Novelty.** Classical (the Bezoutian and the Wronskian of a pencil of binary quadratics); routine.
-- source:
--   Classical: two binary quadratics with non-zero resultant and their Wronskian span the binary quadratics. Uses DiazModulus.quadratic_pencil_wronskian_identities and DiazModulus.quadratic_pencil_resultant_ne_zero. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem quadratic_pencil_wronskian_span {K : Type*} [Field K] [CharZero K] (p q : K[X])
    (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2) (R : K[X]) (hR : R.natDegree ≤ 2) :
    ∃ a b c : K, R = C a * q + C b * p + C c * (derivative p * q - p * derivative q) := by
  sorry

end DiazModulus
