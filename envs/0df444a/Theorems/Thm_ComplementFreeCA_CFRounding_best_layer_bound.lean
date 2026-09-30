-- Prove2me | Theorems.Thm_ComplementFreeCA_CFRounding_best_layer_bound
-- name    : ComplementFreeCA.CFRounding.best_layer_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:16:20.522647+00:00
-- url     : https://prove2.me/theorems/590dd4e6-16d4-41a7-9de7-ae551fe89717
-- title:
--   Step (iii): the best layer has welfare at least OPT*/(3k)
-- statement:
--   Let $v_1,\dots,v_n$ be normalized, complement-free valuations, let $x$ be any point with LP value $L=\sum_{i,S}x_{i,S}v_i(S)$, and let $k\ge1$. Let $\sigma=(S_1,\dots,S_n)$ be a preallocation in which every item appears in at most $k$ bundles and
--   $$\sum_i v_i(S_i)\ge \tfrac13 L.$$
--   If $r$ with $1\le r\le k$ maximizes $\sum_i v_i(S_i^r)$ over $1\le r\le k$, then
--   $$\sum_i v_i(S_i^r)\ \ge\ \frac{L}{3k}.$$
--
--   With $x$ optimal, $L=OPT^*$, and this is the bound $\sum_i v_i(S^r_i)\ge OPT^*/(3k)$ of step (iii) of the proof of Theorem 3.1: the best layer is a feasible allocation within a factor $3k$ of the fractional optimum.
--
--   **Formalization Note** The statement holds for any $x$ whose value $L$ satisfies the displayed hypothesis; optimality of $x$ is not needed for this step.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 6, §3.1, proof of Theorem 3.1, step (iii)

import Mathlib
import Definitions.Def_ComplementFreeCA_CFRounding_Auction
import Definitions.Def_ComplementFreeCA_CFRounding_LP
import Definitions.Def_ComplementFreeCA_CFRounding_Algorithm

namespace ComplementFreeCA.CFRounding

theorem best_layer_bound {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hsub : ∀ i, IsSubadditive (v i))
    (x : Fin n → Finset (Fin m) → ℝ) (σ : Fin n → Finset (Fin m)) (k : ℕ) (hk : 1 ≤ k)
    (hcount : ∀ j, count σ j ≤ k) (hval : lpValue v x / 3 ≤ welfare v σ)
    (r : ℕ) (hr : IsBestLayer v σ k r) :
    lpValue v x / (3 * k) ≤ welfare v (fun i => layer σ i r) := by sorry

end ComplementFreeCA.CFRounding
