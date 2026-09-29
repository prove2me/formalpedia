-- Prove2me | Theorems.Thm_ApproxCliqueWidth_Certificate_bw_ge_of_wellLinked
-- name    : ApproxCliqueWidth.Certificate.bw_ge_of_wellLinked
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:32:37.442162+00:00
-- url     : https://prove2.me/theorems/29c279c3-4fe5-4c90-b231-9aeb3825b353
-- title:
--   Theorem 5.1 — a well-linked set of size $k$ forces $\mathrm{bw}(f) \ge k/3$ ($k \ne 1$)
-- statement:
--   Let $V$ be a finite set with $|V| \ge 2$ and $f : 2^V \to \mathbb{Z}$ a symmetric submodular function with $f(\emptyset) = 0$. Let $k \ne 1$ be a nonnegative integer. If $W \subseteq V$ is well-linked with respect to $f$ and $|W| = k$, then every branch-decomposition $(T, L)$ of $f$ has an edge of width at least $k/3$; that is,
--   $$\mathrm{bw}(f) \ge \frac{k}{3}.$$
--
--   Together with Theorem 5.2 this makes well-linked sets a certificate of large branch-width: a well-linked set of size $3k+1$ shows $\mathrm{bw}(f) > k$.
--
--   **Formalization Note** The conclusion is stated as "every branch-decomposition has an edge $uw$ with $k \le 3 f(A_{uw})$", with no division. The hypothesis $k \ne 1$ corrects a misprint in the paper's statement: every singleton is well-linked, but the edgeless graph on two vertices has cut-rank identically $0$ and hence rank-width $0 < 1/3$, so the printed statement fails for $k = 1$ (the proof's step "$f(\{w\}) \ge 1$" needs $|W| \ge 2$). The statement is otherwise the paper's, and the mission's goal uses it only for sets of size $3k+1 \ge 4$.
-- source:
--   Oum and Seymour, Approximating clique-width and branch-width, J. Combin. Theory Ser. B 96 (2006) 514–528, p. 519, Theorem 5.1 (proof pp. 519–520)

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_BranchDecomp

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour Theorem 5.1 (p. 519), with the misprint for `k = 1` corrected by the hypothesis
`k ≠ 1`: every branch-decomposition of `f` has an edge of width at least `k / 3`. -/
theorem bw_ge_of_wellLinked {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 2 ≤ Fintype.card V) (f : Finset V → ℤ) (hsym : IsSymmetric f) (hsub : IsSubmodular f)
    (h0 : f ∅ = 0) (k : ℕ) (hk : k ≠ 1) (W : Finset V) (hWcard : W.card = k)
    (hW : IsWellLinked f W) :
    ∀ D : BranchDecomp V, ∃ u w : Fin D.n, D.T.Adj u w ∧ (k : ℤ) ≤ 3 * f (D.side u w) := by sorry

end ApproxCliqueWidth.Certificate
