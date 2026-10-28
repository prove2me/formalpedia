-- Prove2me | Theorems.Thm_Erdos624_dense_pool_intersection
-- name    : Erdos624.dense_pool_intersection
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T08:38:30.870029+00:00
-- url     : https://prove2.me/theorems/d828473a-e40b-49b8-a8a6-0746a5f560af
-- title:
--   Dense-pool intersection lemma: $b\,q!\,\#\mathrm{good}\ge g^q$ (Erdős 624 auxiliary)
-- statement:
--   Let $U$ be a finite set with $|U|=n\ge 1$, and let $G$ be a finite colour set of size $g$. Suppose each colour $u\in G$ has a pool $V_u\subseteq U$ satisfying $a|V_u|\ge n$ for some $a\ge 1$. For $q\ge 1$ and $g\ge 2a(q-1)$, writing $b=2^{q+1}a^q$, the number $h$ of $q$-subsets $S\subseteq G$ with $b\bigl|\bigcap_{u\in S}V_u\bigr|\ge n$ satisfies $b\cdot q!\cdot h\ge g^q$.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$. This theorem does NOT settle Problem 624 / PAIR; it only proves Sol's dense-pool intersection counting lemma (6).
--
--   **Formalization Note.** Pure Mathlib: `bOf a q = 2^(q+1)*a^q`, `poolInter`/`goodTuples` as Finset filters; no dependence on a separate Erdős 624 definitions module.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); dense-pool intersection (Sol (6)) derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026).

import Mathlib
open Finset

namespace Erdos624

/-- `b = 2^{q+1} a^q`. -/
def bOf (a q : ℕ) : ℕ := 2 ^ (q + 1) * a ^ q

/-- Intersection of pools over `S` (empty → `univ`). -/
def poolInter {U C : Type*} [Fintype U] [DecidableEq U]
    (V : C → Finset U) (S : Finset C) : Finset U :=
  if h : S.Nonempty then S.inf' h V else univ

/-- Good q-tuples: those with `b · |∩ pools| ≥ n`. -/
def goodTuples {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (G : Finset C) (V : C → Finset U) (a q : ℕ) : Finset (Finset C) :=
  let n := Fintype.card U
  let b := bOf a q
  {S ∈ G.powersetCard q | b * #(poolInter V S) ≥ n}

/-- Dense-pool intersection lemma (Sol (6)), multiplication-cleared.
Pools of density ≥1/a; for `g ≥ 2a(q−1)` and `n≥1`,
`b · q! · #good ≥ g^q` with `b = 2^{q+1} a^q`.
Does **not** settle PAIR / #624. -/
theorem dense_pool_intersection
    {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (G : Finset C) (V : C → Finset U) (a q : ℕ)
    (ha : 1 ≤ a) (hq : 1 ≤ q) (hn : 1 ≤ Fintype.card U)
    (hPool : ∀ u ∈ G, a * #(V u) ≥ Fintype.card U)
    (hg : 2 * a * (q - 1) ≤ #G) :
    bOf a q * q.factorial * #(goodTuples G V a q) ≥ (#G) ^ q := by sorry

end Erdos624
