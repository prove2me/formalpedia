-- Prove2me | Theorems.Thm_ApproxCliqueWidth_Certificate_rwd_le_cwd_le
-- name    : ApproxCliqueWidth.Certificate.rwd_le_cwd_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:35:14.32154+00:00
-- url     : https://prove2.me/theorems/f5be0766-81c9-4871-88af-e6d313948e03
-- title:
--   Proposition 6.3 — $\mathrm{rwd}(G) \le \mathrm{cwd}(G) \le 2^{\mathrm{rwd}(G)+1} - 1$
-- statement:
--   For every finite simple graph $G$,
--   $$\mathrm{rwd}(G) \le \mathrm{cwd}(G) \le 2^{\mathrm{rwd}(G)+1} - 1.$$
--   Concretely:
--
--   1. if $G$ has a $k$-expression, then $G$ has rank-width at most $k$;
--   2. if $G$ has at least one vertex and rank-width at most $k$, then $G$ has a $(2^{k+1} - 1)$-expression.
--
--   Rank-width and clique-width are therefore bounded in terms of each other, which transfers the approximation algorithm for rank-width to clique-width.
--
--   **Formalization Note** "Rank-width at most $k$" is $\mathrm{bw}(\mathrm{cutrk}_G) \le k$ in the predicate form of the branch-decomposition definition; "$\mathrm{cwd}(G) \le m$" is "$G$ has an $m$-expression". Because both predicates are monotone in the bound, the two items are equivalent to the two inequalities. The nonemptiness assumption in item 2 excludes the graph with no vertex, for which clique-width is undefined (it has no $k$-expression for any $k$). $2^{k+1} - 1$ is natural-number subtraction, which is exact since $2^{k+1} \ge 1$.
-- source:
--   Oum and Seymour, Approximating clique-width and branch-width, J. Combin. Theory Ser. B 96 (2006) 514–528, p. 522, Proposition 6.3 (proof pp. 522–524)

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_BranchDecomp
import Definitions.Def_ApproxCliqueWidth_Certificate_KExpr
import Definitions.Def_ApproxCliqueWidth_Certificate_CutRank

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour Proposition 6.3 (p. 522): `rwd(G) ≤ cwd(G) ≤ 2^{rwd(G)+1} - 1`, stated with
the predicates `HasKExpr G k` (`cwd(G) ≤ k`) and `BwLE (cutrk G) k` (`rwd(G) ≤ k`). -/
theorem rwd_le_cwd_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∀ k : ℕ, HasKExpr G k → BwLE (cutrk G) k) ∧
    (Nonempty V → ∀ k : ℕ, BwLE (cutrk G) k → HasKExpr G (2 ^ (k + 1) - 1)) := by sorry

end ApproxCliqueWidth.Certificate
