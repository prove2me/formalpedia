-- Prove2me | Theorems.Thm_ApproxCliqueWidth_Certificate_clique_width_certificate
-- name    : ApproxCliqueWidth.Certificate.clique_width_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:35:45.992423+00:00
-- url     : https://prove2.me/theorems/a1216a2a-d082-49ac-a0a3-999d776b7827
-- title:
--   Theorem 1.1 (certificate form) — a well-linked set of size $3k+1$ certifies $\mathrm{cwd}(G) > k$; without one, $G$ has a $(2^{3k+2}-1)$-expression
-- statement:
--   Let $G$ be a finite simple graph with at least one vertex, let $\mathrm{cutrk}_G$ be its cut-rank function, and let $k \ge 1$ be an integer.
--
--   1. If some set $W$ of $3k + 1$ vertices is well-linked with respect to $\mathrm{cutrk}_G$, then $G$ has no $k$-expression, i.e. $\mathrm{cwd}(G) \ge k + 1$.
--   2. If no set of $3k + 1$ vertices is well-linked with respect to $\mathrm{cutrk}_G$, then $G$ has a $(2^{3k+2} - 1)$-expression, i.e.
--   $$\mathrm{cwd}(G) \le 2^{3k+2} - 1.$$
--
--   This is the mathematical content of Oum and Seymour's Theorem 1.1: the algorithm either finds a well-linked set of size $3k+1$ for the cut-rank function, which certifies that the clique-width exceeds $k$, or builds a decomposition from which a $(2^{3k+2}-1)$-expression is obtained.
--
--   **Formalization Note** The paper's Theorem 1.1 also asserts that the algorithm runs in time $O(n^9 \log n)$; this item does not formalize running time. Without the running time, the dichotomy "$\mathrm{cwd}(G) \ge k+1$ or $\mathrm{cwd}(G) \le 2^{3k+2}-1$" holds for every graph and carries no content, which is why the item states the certificate: the same explicit well-linked-set condition decides which side holds. Labels $\{1,\dots,k\}$ are `Fin k`; "$\mathrm{cwd}(G) \le m$" is "$G$ has an $m$-expression". The nonempty-vertex-set assumption excludes the empty graph, which has no $k$-expression for any $k$. $2^{3k+2}-1$ is exact natural-number subtraction.
-- source:
--   Oum and Seymour, Approximating clique-width and branch-width, J. Combin. Theory Ser. B 96 (2006) 514–528, p. 516, Theorem 1.1; certificate form from p. 521 (remark after Theorem 5.2), p. 524 Corollary 6.4, p. 525 Corollary 6.5

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_KExpr
import Definitions.Def_ApproxCliqueWidth_Certificate_CutRank

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour Theorem 1.1 (p. 516) / Corollary 6.5 (p. 525), certificate form (running time not
formalized). (a) A set of size `3k + 1` well-linked with respect to `cutrk_G` certifies
`cwd(G) ≥ k + 1`; (b) if there is none, `G` has a `(2^{3k+2} - 1)`-expression. -/
theorem clique_width_certificate {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k) :
    ((∃ W : Finset V, W.card = 3 * k + 1 ∧ IsWellLinked (cutrk G) W) → ¬ HasKExpr G k) ∧
    ((¬ ∃ W : Finset V, W.card = 3 * k + 1 ∧ IsWellLinked (cutrk G) W) →
        HasKExpr G (2 ^ (3 * k + 2) - 1)) := by sorry

end ApproxCliqueWidth.Certificate
