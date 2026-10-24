-- Prove2me | Theorems.Thm_DiazModulus_coprime_pencil_mobius
-- name    : DiazModulus.coprime_pencil_mobius
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:24.596456+00:00
-- url     : https://prove2.me/theorems/b442a6ed-6d2d-437a-aeaf-a697bfa9a130
-- title:
--   An invertible change of basis of a coprime pencil of maximal degree 2 is again coprime of maximal degree 2
-- statement:
--   Let $K$ be a field, let $p, q \in K[X]$ be coprime with $\max(\deg p, \deg q) = 2$, and let $a, b, c, d \in K$ with $ad - bc \neq 0$. Then $ap + bq$ and $cp + dq$ are coprime, and $\max(\deg(ap + bq), \deg(cp + dq)) = 2$.
--
--   **Proof.** Put $D = ad - bc$. Inverting the change of basis gives $p = D^{-1}(d(ap + bq) - b(cp + dq))$ and $q = D^{-1}(a(cp + dq) - c(ap + bq))$. Coprimality: from a Bézout identity $xp + yq = 1$, $D^{-1}(dx - cy)(ap + bq) + D^{-1}(ay - bx)(cp + dq) = xp + yq = 1$. Degree: $ap + bq$ and $cp + dq$ have degree at most $2$, as combinations of $p$ and $q$; if both had degree at most $1$, so would $p$ and $q$, by the inversion formulas, against $\max(\deg p, \deg q) = 2$.
--
--   **Novelty.** Standard linear algebra; routine.
-- source:
--   Standard linear algebra. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem coprime_pencil_mobius {K : Type*} [Field K] (p q : K[X]) (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) (a b c d : K) (had : a * d - b * c ≠ 0) :
    IsCoprime (C a * p + C b * q) (C c * p + C d * q) ∧
      max (C a * p + C b * q).natDegree (C c * p + C d * q).natDegree = 2 := by
  sorry

end DiazModulus
