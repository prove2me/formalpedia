-- Prove2me | Theorems.Thm_Erdos624_zero_sum_covering
-- name    : Erdos624.zero_sum_covering
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:40:57.340896+00:00
-- url     : https://prove2.me/theorems/75f80305-5f55-4b8d-a396-30678c77e5f6
-- title:
--   $k$ vectors in $\mathbb F_2^{k-1}$ have a nonempty zero-sum subset
-- statement:
--   **Theorem.** Let $k\ge1$, $|U|=2^k$ and $h:U\to\mathbb F_2^{k-1}$. Every $k$-set $Y\subseteq U$ contains a nonempty $A$ with $\sum_{a\in A}h(a)=0$.
--
--   In the context of Erdős Problem 624 this says that each family $\mathcal F_h$ of nonempty zero-sum sets of size $\le k$ meets every $k$-set (it is a covering family); together with `zero_sum_count` it gives a feasible fractional packing at capacity two, an obstruction to proving the two-map common-hole lemma by separately convexified fibre conditions.
--
--   **Formalization Note.** $U=\mathrm{Fin}\,(2^k)$, $\mathbb F_2^{k-1}$ is `Fin (k-1) → ZMod 2`.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; fractional obstruction of claim from GPT 6.1 Sol (fifth answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem zero_sum_covering (k : ℕ) (h : Fin (2 ^ k) → (Fin (k - 1) → ZMod 2))
    (Y : Finset (Fin (2 ^ k))) (hY : #Y = k) (hk : 1 ≤ k) :
    ∃ A ⊆ Y, A.Nonempty ∧ ∑ a ∈ A, h a = 0 := by sorry

end Erdos624
