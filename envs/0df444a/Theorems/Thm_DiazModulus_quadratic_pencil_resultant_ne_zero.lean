-- Prove2me | Theorems.Thm_DiazModulus_quadratic_pencil_resultant_ne_zero
-- name    : DiazModulus.quadratic_pencil_resultant_ne_zero
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:46.696458+00:00
-- url     : https://prove2.me/theorems/71979ac5-d1c9-4fad-8dc4-65c8e2670d78
-- title:
--   A coprime pair of polynomials of maximal degree 2 has non-zero resultant [20]² − [21][10] (characteristic zero)
-- statement:
--   Let $K$ be a field of characteristic zero and $p, q \in K[X]$ coprime (that is, $ap + bq = 1$ for some $a, b \in K[X]$) with $\max(\deg p, \deg q) = 2$. Write $p_i, q_i$ for the coefficients of $X^i$ and $[ij] = p_iq_j - p_jq_i$. Then $\mathrm{Res} = [20]^2 - [21][10] \neq 0$, that is, $(p_2q_0 - p_0q_2)^2 - (p_2q_1 - p_1q_2)(p_1q_0 - p_0q_1) \neq 0$.
--
--   Up to sign, $\mathrm{Res}$ is the determinant of the Bezout matrix of $p$ and $q$, their resultant as binary quadratic forms.
--
--   **Proof.** By `DiazModulus.quadratic_pencil_wronskian_identities`, $J = p'q - pq' = [21]X^2 + 2[20]X + [10]$, so the matrix whose rows are the coefficient vectors of $q$, $p$ and $J$ in the basis $(1, X, X^2)$ has determinant $-2\,\mathrm{Res}$. If $\mathrm{Res} = 0$, a non-zero vector $(v_0, v_1, v_2)$ kills this matrix from the left, that is, $v_0q + v_1p + v_2J = 0$. If $v_2 = 0$, one of $p, q$ is a constant multiple of the other; coprimality makes the other a unit, and both have degree $0$, against $\max(\deg p, \deg q) = 2$. If $v_2 \neq 0$, the relation reads $(v_2p' + v_0)q = p(v_2q' - v_1)$, so by coprimality $p$ divides $v_2p' + v_0$ and $q$ divides $v_2q' - v_1$. Whichever of $p, q$ has degree $2$ then divides a polynomial of degree at most $1$, which must be $0$; but its coefficient of $X$ is $2v_2$ times the leading coefficient, which is non-zero in characteristic zero.
--
--   **Novelty.** Classical (the Bezoutian and the Wronskian of a pencil of binary quadratics); routine.
-- source:
--   Classical: the resultant of two binary quadratics (up to sign the determinant of their Bezout matrix) vanishes only when they have a common factor. Uses DiazModulus.quadratic_pencil_wronskian_identities. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem quadratic_pencil_resultant_ne_zero {K : Type*} [Field K] [CharZero K] (p q : K[X])
    (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2) :
    (p.coeff 2 * q.coeff 0 - p.coeff 0 * q.coeff 2) ^ 2
      - (p.coeff 2 * q.coeff 1 - p.coeff 1 * q.coeff 2) * (p.coeff 1 * q.coeff 0 - p.coeff 0 * q.coeff 1) ≠ 0 := by
  sorry

end DiazModulus
