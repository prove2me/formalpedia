-- Prove2me | Theorems.Thm_BitcoinOligopoly_EoS_theorem_2
-- name    : BitcoinOligopoly.EoS.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:29.289569+00:00
-- url     : https://prove2.me/theorems/44fb40f1-dcc6-433c-8729-c3c822e0c215
-- title:
--   Theorem 2 — equilibrium market-share lower bound under economies of scale
-- statement:
--   Consider the economies-of-scale contest with $n\ge2$ miners, exponent $\alpha\ge1$, and positive unit costs $c_i$. Let $q$ be any pure Nash equilibrium. For any miners $i$ and $j$, including $i=j$, if both invest a positive amount, then
--
--   $$
--   x_i(q)\ge 1-\frac1\alpha\frac{c_i}{c_j}.
--   $$
--
--   The bound relates a participant's share to its unit cost relative to any other participant's. Taking $i=j$ gives the cost-independent lower bound in Corollary 4.
--
--   **Formalization Note** The equilibrium predicate quantifies over all nonnegative unilateral deviations. No existence of equilibrium is assumed beyond the chosen $q$; no ordering of the cost vector or distinctness of $i,j$ is imposed.
-- source:
--   Arnosti & Weinberg, Bitcoin: A Natural Oligopoly, arXiv:1811.08572v1, p. 9 (PDF 10), Theorem 2

import Mathlib
import Definitions.Def_BitcoinOligopoly_EoS_Model

namespace BitcoinOligopoly.EoS

/-- Theorem 2, p. 9 (PDF 10): a lower share bound for any two participating miners. -/
theorem theorem_2 {n : ℕ} (P : Params n) (hP : P.Standing) (q : Fin n → ℝ)
    (hq : IsEquilibrium P q) (i j : Fin n) (hi : 0 < q i) (hj : 0 < q j) :
    1 - (1 / P.α) * (P.c i / P.c j) ≤ share P q i := by sorry

end BitcoinOligopoly.EoS
