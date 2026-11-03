-- Prove2me | Theorems.Thm_BFVBound_G_le_geom
-- name    : BFVBound.G_le_geom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T15:41:04.504611+00:00
-- url     : https://prove2.me/theorems/d7a8bcd1-f063-4fe2-b0ab-c678a4679728
-- title:
--   The BFV hypergeometric factor is dominated by $1/(1-x)$
-- statement:
--   **The hypergeometric factor is dominated by a geometric series.**
--
--   With $G(x)=\sum_{n\ge0}a_nx^n$, $a_n=\big((\tfrac12)_n\big)^2/\big((2)_n\,n!\big)$, the coefficients satisfy
--   $a_0=1$ and $a_{n+1}/a_n=(n+\tfrac12)^2/((n+1)(n+2))\le1$, so $0\le a_n\le 1$ for every $n$. Hence, for
--   $0\le x<1$,
--   $$G(x)=\sum_n a_n x^n\ \le\ \sum_n x^n=\frac{1}{1-x}.$$
--   Comparing the two nonnegative series term by term (both converge) gives the claim. This is the crude upper
--   bound on the BFV product expectation used whenever a rounding algorithm's per-edge energy must be compared
--   with the SDP bound from above; the matching lower bound $G\ge1+x/8$ is the content of the sibling nodes.
-- source:
--   Anshu, Lee, Mousavi, Parekh, Soleimanifar, arXiv:2504.15276 Section 4.2 Eq. (17); Parekh-Thompson arXiv:2110.07781 Eq. (3); Brandao-Fernandes-Vallentin arXiv:0910.5765; G = 2F1(1/2,1/2;2;.) is the hypergeometric factor of the rank-three product rounding.

import Mathlib
import Definitions.Def_QuantumMaxCutBFVProductRounding
open scoped BigOperators

namespace BFVBound

theorem G_le_geom (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) : G x ≤ 1 / (1 - x) := by sorry

end BFVBound
