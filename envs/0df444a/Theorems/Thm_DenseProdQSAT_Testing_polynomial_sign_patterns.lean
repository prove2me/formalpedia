-- Prove2me | Theorems.Thm_DenseProdQSAT_Testing_polynomial_sign_patterns
-- name    : DenseProdQSAT.Testing.polynomial_sign_patterns
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:09.953209+00:00
-- url     : https://prove2.me/theorems/86fe0e1c-c232-4e71-b13b-781e8bc376d9
-- title:
--   Theorem 4.5 — ternary polynomial sign-pattern bound
-- statement:
--   Let $p_1,\ldots,p_s$ be real polynomials in $r$ real variables, each of total degree at most $D$, where $D\ge1$ and $s\ge r\ge1$. Counting zero as a separate sign gives
--
--   $$\left|\{(\operatorname{sgn}p_1(x),\ldots,\operatorname{sgn}p_s(x)):x\in\mathbb R^r\}\right|\le\left(\frac{8eDs}{r}\right)^r.$$
--
--   The result controls the finite sign descriptions used by the two algebraic complexity bounds. The realized sign set is finite because it lies in a set of $3^s$ vectors; its cardinality is not a default value for an infinite set.
--
--   Differences from the source:
--   - encoding: sign labels -1, 0, 1 → three finite labels for negative, zero, positive; reason: a bijection preserves the number of realized sign vectors
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), Theorem 4.5, p. 13

import Definitions.Def_DenseProdQSAT_Testing_Algebra
set_option autoImplicit false

namespace DenseProdQSAT.Testing

theorem polynomial_sign_patterns (r s D : ℕ) (hr : 1 ≤ r) (hs : r ≤ s) (hD : 1 ≤ D)
    (p : Fin s → MvPolynomial (Fin r) ℝ) (hp : ∀ j, (p j).totalDegree ≤ D) :
    ((Set.range (fun x : Fin r → ℝ => fun j : Fin s =>
      TernarySign (MvPolynomial.eval x (p j)))).ncard : ℝ) ≤
        (8 * Real.exp 1 * D * s / r) ^ r := by sorry

end DenseProdQSAT.Testing
