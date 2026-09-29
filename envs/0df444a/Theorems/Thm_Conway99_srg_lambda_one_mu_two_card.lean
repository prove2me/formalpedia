-- Prove2me | Theorems.Thm_Conway99_srg_lambda_one_mu_two_card
-- name    : Conway99.srg_lambda_one_mu_two_card
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T16:13:48.123095+00:00
-- url     : https://prove2.me/theorems/feb32f7e-d5eb-4982-ad87-56cf5f155ad7
-- title:
--   Counting identity for $\lambda = 1$, $\mu = 2$: $2n = k^2 + 2$
-- statement:
--   Let $g$ be a strongly regular graph on a nonempty finite vertex set with parameters $(n,k,\lambda,\mu) = (n,k,1,2)$: it has $n$ vertices, every vertex has exactly $k$ neighbours, adjacent vertices have exactly one common neighbour, and distinct non-adjacent vertices have exactly two common neighbours. Then
--
--   $$2n = k^2 + 2 .$$
--
--   This is the standard path-counting identity $k(k - \lambda - 1) = (n - k - 1)\mu$ for strongly regular graphs, specialised to $\lambda = 1$ and $\mu = 2$. With $k = 14$ it forces $n = 99$, which is where the parameter set of Conway's problem comes from. The hypothesis $0 < n$ excludes the empty vertex set, for which the conditions hold vacuously.
-- source:
--   Counting identity for strongly regular graphs, specialised to lambda = 1, mu = 2; cf. Mathlib SimpleGraph.IsSRGWith.param_eq and https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

open SimpleGraph

namespace Conway99

theorem srg_lambda_one_mu_two_card {V : Type*} [Fintype V] {g : SimpleGraph V}
    [DecidableRel g.Adj] {n k : ℕ} (h : g.IsSRGWith n k 1 2) (hn : 0 < n) :
    2 * n = k ^ 2 + 2 := by sorry

end Conway99
