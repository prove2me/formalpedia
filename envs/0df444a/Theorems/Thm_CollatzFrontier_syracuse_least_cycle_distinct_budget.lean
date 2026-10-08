-- Prove2me | Theorems.Thm_CollatzFrontier_syracuse_least_cycle_distinct_budget
-- name    : CollatzFrontier.syracuse_least_cycle_distinct_budget
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-04T17:36:15.271727+00:00
-- url     : https://prove2.me/theorems/2c44fd94-5536-4e7f-85aa-93c9f3758d2f
-- title:
--   A distinct-state product budget for realized least-period Syracuse cycles
-- statement:
--   Let $m$ be a positive integer whose Syracuse orbit $T(n)=\operatorname{oddpart}(3n+1)=(3n+1)/2^{v_2(3n+1)}$ has **least** (not merely some) period $p>0$: $T^p(m)=m$, and no $0<k<p$ satisfies $T^k(m)=m$. Suppose every state on this cycle is at least a fixed positive bound $B$: $T^i(m) \ge B$ for all $i<p$. Let $K=\sum_{i<p}v_2(3T^i(m)+1)$ be the total 2-adic valuation accumulated around the cycle. Then
--
--   $$2^K \prod_{i<p}(B+2i) \;\le\; \prod_{i<p}\bigl(3(B+2i)+1\bigr).$$
--
--   The accepted platform theorem [`syracuse_cycle_min_upper_bound`](https://prove2.me/theorems/514577b7-9148-4a35-a0b2-80ac16b8b322) bounds the same kind of product using only the bare minimum $B=\min_i T^i(m)$ repeated $p$ times; it does not exploit that the $p$ states of a least-period cycle are pairwise distinct. Since all states are odd, distinctness forces the sorted states to be spaced at least $2$ apart, i.e. at least $B, B+2, B+4, \dots, B+2(p-1)$ — strictly more than $p$ copies of the bare minimum. This theorem replaces the repeated-minimum envelope with the sharper spaced envelope, giving a strictly tighter necessary condition on any realized cycle (for $p \ge 2$). It is purely a strengthening of the known bound: it assumes a nontrivial cycle rather than asserting one exists, and it makes no claim about realizability of any particular word or period.
--
--   **Formalization Note.** Least period is expressed by `hcyc` together with `hmin`; `B>0` is assumed for convenience.
-- source:
--   Original contribution of this submission, from the private repository collatz-frontier, commit 4d656b9c9c5815305bd391f206c9d3e9587dd395 (branch main), file lean/CollatzFrontier/DistinctCycleBudget.lean, declaration CollatzFrontier.syracuse_least_cycle_distinct_budget (also documented in docs/distinct-cycle-budget.md). Compares with the accepted platform theorem syracuse_cycle_min_upper_bound, https://prove2.me/theorems/514577b7-9148-4a35-a0b2-80ac16b8b322, which uses only the orbit minimum and does not exploit distinctness of odd cycle states.

import Mathlib
import Definitions.Def_syracuseStep

namespace CollatzFrontier

theorem syracuse_least_cycle_distinct_budget (m p B : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hBpos : 0 < B) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m)
    (hbaseline : ∀ i < p, B ≤ syracuseStep^[i] m) :
    2 ^ (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) *
      (∏ i ∈ Finset.range p, (B + 2 * i)) ≤
      ∏ i ∈ Finset.range p, (3 * (B + 2 * i) + 1) := by sorry

end CollatzFrontier
