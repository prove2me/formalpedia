-- Prove2me | Theorems.Thm_CappedBaseStock_greedy_window
-- name    : CappedBaseStock.greedy_window
-- status  : Proved
-- author  : @StellaXin
-- created : 2026-09-08T01:47:58.521711+00:00
-- url     : https://prove2.me/theorems/c26f6689-f6b9-4882-a542-20c5ce412e2f
-- title:
--   Lemma 2 — Greedy recursion on a consecutive block
-- statement:
--   Fix an integer $L\ge1$ and two nonnegative real sequences $(a_t)_{t\in\mathbb Z}$ and $(b_t)_{t\in\mathbb Z}$. Suppose that, for every integer $t$,
--
--   $$a_t=\left(b_t-\sum_{i=1}^{L}a_{t-i}\right)^+.$$
--
--   Then, for every integer starting index $s$ and every integer length $1\le n\le L+1$,
--
--   $$\sum_{j=0}^{n-1}a_{s+j}\le\max_{0\le j<n}b_{s+j}.$$
--
--   The recurrence includes the terms preceding the block; they are not reset to zero at its beginning. Blocks are nonempty so their ordinary finite maximum is defined. No inventory, independence, or expectation hypotheses are needed.
-- source:
--   Linwei Xin, Capped Base-Stock Policies: A 2.33-Approximation, author-supplied LaTeX manuscript (756 lines); public paper listing https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7134538 . Author-supplied source SHA-256: f353793c255e1ebed5f3ec541037284bd926183e3e5b71941f13e79c2d67cb7a. Lemma 2 (`lem-greedy-window`), lines 502–512.

import Mathlib

open scoped BigOperators

namespace CappedBaseStock


theorem greedy_window
    (L : ℕ) (hL : 1 ≤ L)
    (a b : ℤ → ℝ)
    (ha : ∀ t : ℤ, 0 ≤ a t)
    (hb : ∀ t : ℤ, 0 ≤ b t)
    (hrec : ∀ t : ℤ,
      a t = max (b t - ∑ i ∈ Finset.Icc 1 L, a (t - (i : ℤ))) 0)
    (start : ℤ) (n : ℕ) (hn : 0 < n) (hlen : n ≤ L + 1) :
    (∑ i ∈ Finset.range n, a (start + (i : ℤ))) ≤
      (Finset.range n).sup'
        (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn))
        (fun i => b (start + (i : ℤ))) := by sorry

end CappedBaseStock
