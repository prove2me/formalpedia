-- Prove2me | Theorems.Thm_CClosedGraphs_Improved_claim_3_3
-- name    : CClosedGraphs.Improved.claim_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:21:42.507883+00:00
-- url     : https://prove2.me/theorems/6b968867-645a-4bdc-8aa4-c3f4d1aaac7a
-- title:
--   Claim 3.3, p. 11 — (1 − x)^k ≤ 1 − xk/2 for 0 < x ≤ 1/2, 1 ≤ k ≤ 2
-- statement:
--   For all real numbers $x$ and $k$ with $0<x\le 1/2$ and $1\le k\le 2$,
--   $$(1-x)^k\le 1-\frac{xk}{2}.$$
--
--   The paper applies it with $x=\Delta(G)/n$ and $k=2-2^{1-c}$ to bound the term $(n-\Delta(G))^{2-2^{1-c}}$ in the recurrence.
--
--   **Formalization Note** $(1-x)^k$ is the real power with real exponent $k$.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 11, Claim 3.3

import Mathlib

namespace CClosedGraphs.Improved
theorem claim_3_3 (x k : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) (hk1 : 1 ≤ k) (hk2 : k ≤ 2) :
    (1 - x) ^ k ≤ 1 - x * k / 2 := by sorry
end CClosedGraphs.Improved
