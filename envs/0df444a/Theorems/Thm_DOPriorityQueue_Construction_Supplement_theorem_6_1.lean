-- Prove2me | Theorems.Thm_DOPriorityQueue_Construction_Supplement_theorem_6_1
-- name    : DOPriorityQueue.Construction.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:43:49.826628+00:00
-- url     : https://prove2.me/theorems/13e347e3-34de-4cbe-a56b-896efe8f8cc9
-- title:
--   Theorem 6.1 — fixed-history probe lower bound and finite-parameter estimates
-- statement:
--   For an eventually bounded family $\varepsilon_n$ and a family $\delta_n\to0$, there is a threshold uniform over horizons, memory sizes, priority universes and implementations. For all $n$ beyond it, all $2n\le T$, $1\le M\le n/2$, and all priority domains containing $[n]$, consider an exact online opaque-token queue with at most $M$ private words, including registers and retained answers. Every execution terminates, tokens first arrive at their insertions, and answers return from private memory. Only insertion-record replacement privacy is assumed, with public operation types fixed.
--
--   There is one fixed vector $X\in[n]^n$, hence one fixed history $\sigma(X)$ of exactly $2n$ operations, for which
--   $$\mathbb E_Q[P(\sigma(X))]\ge\frac{n\log_2n}{32\log_2(M+2)}.$$
--   The expectation is over internal randomness alone; the history is selected before the random tape. This gives the printed $\Omega(n\log n/\log(M+2))$ bound on an $O(n)$-operation history. All $M$ in the stated range and both probe-ratio regimes are retained. Arbitrary free local computations are permitted.
--
--   The statement also includes the finite-parameter estimates used in the proof, for every admissible finite $\varepsilon,\delta$:
--   $$\mathbb E_{X,Q}[P]\ge\frac{n(\log_2n-2-\gamma_n)}{\log_2(2(M+2))}-2n,\qquad P\ge n-M\text{ on every execution},$$
--   where $\gamma_n=(\varepsilon+1)/\ln2+\delta\log_2n/(1-e^{-1})$. Infinite expected probes are included. The threshold depends on the privacy families, never on $T,M$ or the implementation. This companion theorem is the independent lower bound; it is not a step in the proof of the retained construction goal.
--
--   Differences from the source:
--   - generalization: w=Theta(log T) balls-and-bins queues → all word sizes in the larger opaque controller model, with atomic free numeric maps and public numeric initialization; reason: the proof uses only token conservation and M private slots and covers every source implementation
--   - generalization: an asymptotic Omega bound on an O(n)-operation fixed history → a fixed history of exactly 2n calls with coefficient 1/32, plus equation (15) and the pathwise n-M bound; reason: page 30 proves the pointwise estimates and both ratio regimes give the uniform factor 1/32; no source conclusion is removed
--   - encoding: epsilon=O(1), delta=o(1) → eventually bounded epsilon_n and delta_n tending to zero as n tends to infinity, with a threshold before every admissible T,M,U,w and queue; reason: makes the asymptotic and uniform quantifiers explicit without imposing n=Theta(T)
--   - encoding: fixed distinct opaque tokens and priorities in [n] → canonical natural token labels and Fin n priorities shifted by one; reason: token relabeling and index translation preserve every instance; no token identity is available to the controller
--   - encoding: expectations possibly infinite and signed finite-parameter lower bound → extended nonnegative sums and ofReal of real lower bounds; reason: handles infinite probes and maps negative lower bounds to the equivalent zero bound
-- source:
--   Zimai Guo, Cheng Hong, Zhechen Li, STOC 2027 submission #538 (October 2026), p. 27; proof pp. 28–30, Theorem 6.1

import Definitions.Def_DOPriorityQueue_Construction_Supplement_LowerBound

set_option autoImplicit false

namespace DOPriorityQueue.Construction.Supplement

/-- Guo--Hong--Li, p. 27, Theorem 6.1, with the finite-parameter bounds
from its proof on p. 30. The fixed history has exactly 2n operations. -/
theorem theorem_6_1 : LowerBoundTarget ∧ PointwiseLowerBound := by sorry

end DOPriorityQueue.Construction.Supplement
