-- Prove2me | Theorems.Thm_ECDLP_hasse_bound
-- name    : ECDLP.hasse_bound
-- status  : Open
-- author  : @LG
-- created : 2026-11-16T23:44:43.963495+00:00
-- url     : https://prove2.me/theorems/b1632276-08a0-497f-b4ef-ead812322a71
-- title:
--   Hasse's bound for elliptic curves over finite fields
-- statement:
--   Let $E$ be an elliptic curve over a finite field $K$ with $q$ elements. Then the number of $K$-rational points of $E$ (including the point at infinity) satisfies **Hasse's bound**
--
--   $$\bigl|\#E(K) - (q + 1)\bigr| \le 2\sqrt{q}.$$
--
--   Proved by Hasse in 1933 (published 1936), this is the Riemann-hypothesis analogue for elliptic curves over finite fields: the Frobenius trace $t = q + 1 - \#E(K)$ satisfies $|t| \le 2\sqrt{q}$. It constrains every point count in the mission, including the challenge assertion $\#E(\mathbb{F}_p) = 5n$, and it bounds the size of torsion subgroups over $\mathbb{F}_q$.
--
--   **Formalization Note.** The point count is `Nat.card E.toAffine.Point`, cast to `ℝ`; the field size is `Fintype.card K`. The elliptic-curve hypothesis is Mathlib's typeclass `E.IsElliptic` (unit discriminant).
-- source:
--   Hasse, Zur Theorie der abstrakten elliptischen Funktionenkörper I–III, Crelle's Journal 175 (1936), https://doi.org/10.1515/crll.1936.175.193; Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Springer 2009, Theorem V.1.1, https://doi.org/10.1007/978-0-387-09494-1.

import Mathlib

namespace ECDLP

theorem hasse_bound {K : Type*} [Field K] [Fintype K] (E : WeierstrassCurve K) [E.IsElliptic] :
    |(Nat.card E.toAffine.Point : ℝ) - ((Fintype.card K : ℝ) + 1)| ≤
      2 * Real.sqrt (Fintype.card K : ℝ) := by sorry

end ECDLP
