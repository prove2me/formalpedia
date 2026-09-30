-- Prove2me | Theorems.Thm_ComplementFreeCA_ValueQuery_case_one_all_to_one
-- name    : ComplementFreeCA.ValueQuery.case_one_all_to_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:56:59.215709+00:00
-- url     : https://prove2.me/theorems/e7e3b630-e4a3-489d-9302-cd9534e05d53
-- title:
--   Proof of Theorem 5.1, first case — giving all items to the top bidder is a 2√m-approximation
-- statement:
--   Let $v_1,\dots,v_n$ be normalized, monotone, complement-free valuations on bundles of $M=\{1,\dots,m\}$ and let $O=(O_1,\dots,O_n)$ be an allocation (pairwise disjoint bundles). Call bidder $i$ **large** if $|O_i|\ge\sqrt m$ and **small** if $|O_i|<\sqrt m$. Suppose the large bidders carry at least as much welfare as the small ones:
--   $$\sum_{i\ \mathrm{small}} v_i(O_i)\;\le\;\sum_{i\ \mathrm{large}} v_i(O_i).$$
--   Then for every bidder $i_0$ maximizing $v_i(M)$,
--   $$\sum_{i=1}^n v_i(O_i)\;\le\;2\sqrt m\; v_{i_0}(M).$$
--
--   This is the first case of the proof of Theorem 5.1: there are at most $\sqrt m$ large bidders, so one of them is worth $|OPT|/(2\sqrt m)$, and giving all items to the top bidder achieves it.
--
--   **Formalization Note** The paper writes the conclusion for "the bidder $i$ that maximizes $v_i(O_i)$"; the conclusion here is for a bidder maximizing $v_i(M)$, which is the allocation the algorithm compares, and follows by monotonicity. The allocation $O$ is arbitrary, not only optimal. At $m=0$ the statement holds trivially (all values are $v_i(\emptyset)=0$).
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 11, proof of Theorem 5.1, third and fourth paragraphs (definition of OPT, first case)

import Mathlib
import Definitions.Def_ComplementFreeCA_ValueQuery_Basic

open Finset

namespace ComplementFreeCA.ValueQuery

/-- Proof of Theorem 5.1, first case (p. 11): if the bidders whose bundle has at least `√m`
items carry at least as much welfare as the others, then `|OPT| ≤ 2√m · v_{i₀}(M)` for a bidder
`i₀` maximizing `v_i(M)`. -/
theorem case_one_all_to_one {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsCFValuation (v i)) (O : Fin n → Finset (Fin m)) (hO : IsAllocation O)
    (hcase : ∑ i ∈ univ.filter (fun i => ((O i).card : ℝ) < Real.sqrt m), v i (O i) ≤
      ∑ i ∈ univ.filter (fun i => Real.sqrt m ≤ ((O i).card : ℝ)), v i (O i))
    (i₀ : Fin n) (hi₀ : ∀ i, v i univ ≤ v i₀ univ) :
    welfare v O ≤ 2 * Real.sqrt m * v i₀ univ := by sorry

end ComplementFreeCA.ValueQuery
