-- Prove2me | Theorems.Thm_ApproxCliqueWidth_Certificate_bw_le_of_no_wellLinked
-- name    : ApproxCliqueWidth.Certificate.bw_le_of_no_wellLinked
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:33:01.201783+00:00
-- url     : https://prove2.me/theorems/9e7e7cc9-010d-44ac-9fe0-c623c0320b04
-- title:
--   Theorem 5.2 — no well-linked set of size $k$ implies $\mathrm{bw}(f) \le k$
-- statement:
--   Let $V$ be a finite set and $f : 2^V \to \mathbb{Z}$ a symmetric submodular function with $f(\{v\}) \le 1$ for all $v \in V$ and $f(\emptyset) = 0$, and let $k \ge 0$ be an integer. If there is no set $W \subseteq V$ of size $k$ that is well-linked with respect to $f$, then
--   $$\mathrm{bw}(f) \le k.$$
--
--   This is the constructive half of the approximation: absence of the obstruction yields a branch-decomposition of width at most $k$, and together with Theorem 5.1 gives the factor-$3$ approximation of branch-width.
--
--   **Formalization Note** $\mathrm{bw}(f) \le k$ is the predicate of the branch-decomposition definition: $|V| \le 1$ and $f(\emptyset) \le k$ (the paper's convention $\mathrm{bw}(f) = f(\emptyset)$ for $|V|\le1$), or a branch-decomposition of width at most $k$ exists.
-- source:
--   Oum and Seymour, Approximating clique-width and branch-width, J. Combin. Theory Ser. B 96 (2006) 514–528, p. 520, Theorem 5.2 (proof pp. 520–521)

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_BranchDecomp

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour Theorem 5.2 (p. 520): if there is no well-linked set of size `k`, then
`bw(f) ≤ k`. -/
theorem bw_le_of_no_wellLinked {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → ℤ) (hsym : IsSymmetric f) (hsub : IsSubmodular f)
    (hsingle : ∀ v : V, f {v} ≤ 1) (h0 : f ∅ = 0) (k : ℕ)
    (hno : ¬ ∃ W : Finset V, W.card = k ∧ IsWellLinked f W) :
    BwLE f k := by sorry

end ApproxCliqueWidth.Certificate
