-- Prove2me | Theorems.Thm_ComplementFreeCA_ValueQuery_case_two_one_item_each
-- name    : ComplementFreeCA.ValueQuery.case_two_one_item_each
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:57:30.921615+00:00
-- url     : https://prove2.me/theorems/3642dafc-6d0e-4237-b959-bbc94ecf34da
-- title:
--   Proof of Theorem 5.1, second case — a one-item-each allocation is a 2√m-approximation
-- statement:
--   Let $v_1,\dots,v_n$ be normalized, monotone, complement-free valuations on bundles of $M=\{1,\dots,m\}$ and let $O=(O_1,\dots,O_n)$ be an allocation. With large and small bidders as in the first case ($|O_i|\ge\sqrt m$, resp. $|O_i|<\sqrt m$), suppose the small bidders carry strictly more welfare:
--   $$\sum_{i\ \mathrm{large}} v_i(O_i)\;<\;\sum_{i\ \mathrm{small}} v_i(O_i).$$
--   Then there is an allocation $A=(A_1,\dots,A_n)$ with pairwise disjoint bundles and $|A_i|\le 1$ for every $i$ such that
--   $$\sum_{i=1}^n v_i(O_i)\;\le\;2\sqrt m\sum_{i=1}^n v_i(A_i).$$
--
--   This is the second case of the proof of Theorem 5.1: giving each small bidder its most valuable item of $O_i$ yields an allocation of the second kind the algorithm considers, worth at least $|OPT|/(2\sqrt m)$.
--
--   **Formalization Note** The paper's chain uses strict inequalities and divides by $|T_i|$; both fail when some $O_i=\emptyset$ or all values vanish, so the conclusion is stated with $\le$ and without division. The case hypothesis keeps the page's strict inequality.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 12, proof of Theorem 5.1, second case (first paragraph of p. 12)

import Mathlib
import Definitions.Def_ComplementFreeCA_ValueQuery_Basic

open Finset

namespace ComplementFreeCA.ValueQuery

/-- Proof of Theorem 5.1, second case (p. 12): if the bidders whose bundle has fewer than `√m`
items carry strictly more welfare than the others, some allocation giving every bidder at most one
item has welfare at least `|OPT|/(2√m)`. -/
theorem case_two_one_item_each {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsCFValuation (v i)) (O : Fin n → Finset (Fin m)) (hO : IsAllocation O)
    (hcase : ∑ i ∈ univ.filter (fun i => Real.sqrt m ≤ ((O i).card : ℝ)), v i (O i) <
      ∑ i ∈ univ.filter (fun i => ((O i).card : ℝ) < Real.sqrt m), v i (O i)) :
    ∃ A : Fin n → Finset (Fin m), IsAllocation A ∧ (∀ i, (A i).card ≤ 1) ∧
      welfare v O ≤ 2 * Real.sqrt m * welfare v A := by sorry

end ComplementFreeCA.ValueQuery
