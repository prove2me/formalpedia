-- Prove2me | Theorems.Thm_FlowsNetworks_Representatives_sum_of_permutation_matrices
-- name    : FlowsNetworks.Representatives.sum_of_permutation_matrices
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:30.075597+00:00
-- url     : https://prove2.me/theorems/28181b97-1a70-4fbe-b8d8-79c50074fc5b
-- title:
--   Chapter II, Corollary 10.4 — a 0-1 matrix with k ones in each row and column is a sum of k permutation matrices
-- statement:
--   Let $A$ be an $n \times n$ matrix whose entries are the integers $0$ and $1$, and let $k > 0$. If every row and every column of $A$ contains exactly $k$ entries equal to $1$, then there are permutations $\sigma_1, \dots, \sigma_k$ of $\{1, \dots, n\}$ with
--   $$A = P_{\sigma_1} + \dots + P_{\sigma_k},$$
--   where $P_\sigma$ is the permutation matrix of $\sigma$ (entry $1$ at $(i, \sigma(i))$, $0$ elsewhere).
--
--   This is the decomposition of a $k$-regular bipartite graph into $k$ perfect matchings (König's theorem), obtained in the book by repeated application of Corollary 10.3.
--
--   **Formalization Note** $A$ is a `Matrix (Fin n) (Fin n) ℕ` with every entry $0$ or $1$; the statement does not require the permutations to be distinct.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 59, Corollary 10.4

import Mathlib
import Definitions.Def_FlowsNetworks_Representatives_SystemsOfRepresentatives

namespace FlowsNetworks.Representatives

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Corollary 10.4 (p. 59). If `A` is an `n × n`
matrix whose entries are the integers `0` and `1`, with `k > 0` entries `1` in each row and in each
column, then `A` is a sum of `k` permutation matrices. -/
theorem sum_of_permutation_matrices {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) (hk : 0 < k)
    (hrow : ∀ i, (Finset.univ.filter (fun j => A i j = 1)).card = k)
    (hcol : ∀ j, (Finset.univ.filter (fun i => A i j = 1)).card = k) :
    ∃ σ : Fin k → Equiv.Perm (Fin n), A = ∑ l, permMatrix (σ l) := by sorry

end FlowsNetworks.Representatives
