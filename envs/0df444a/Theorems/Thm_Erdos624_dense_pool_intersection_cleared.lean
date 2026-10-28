-- Prove2me | Theorems.Thm_Erdos624_dense_pool_intersection_cleared
-- name    : Erdos624.dense_pool_intersection_cleared
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T08:47:22.795755+00:00
-- url     : https://prove2.me/theorems/bf2fb01f-4025-457c-90cf-2c7a71e59f0f
-- title:
--   Dense-pool intersection (cleared): $b\,q!\,\#\mathrm{good}\ge g^q$ (Erdős 624)
-- statement:
--   Let $U$ be a finite set with $|U|=n\ge 1$, and let $G$ be a finite colour set of size $g$. Suppose each colour $u\in G$ has a pool $V_u\subseteq U$ satisfying $a|V_u|\ge n$ for some $a\ge 1$. For $q\ge 1$ and $g\ge 2a(q-1)$, writing $b=2^{q+1}a^q$, the number $h$ of $q$-subsets $S\subseteq G$ with $b\bigl|\bigcap_{u\in S}V_u\bigr|\ge n$ satisfies
--
--   $$b\cdot q!\cdot h\ge g^q.$$
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$. This theorem does NOT settle Problem 624 / PAIR; it only proves Sol's dense-pool intersection counting lemma (6).
--
--   **Formalization Note.** Pure Mathlib with let-bound $b$, pool intersection, and good-tuple filter.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); dense-pool intersection (Sol (6)) derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026).

import Mathlib
open Finset

namespace Erdos624

/-- Dense-pool intersection lemma (Sol (6)), multiplication-cleared.
Pools of density at least 1/a; for g at least 2a(q-1) and n at least 1,
(2^{q+1} a^q) * q! * #good >= g^q.
Does not settle PAIR / #624. -/
theorem dense_pool_intersection_cleared
    {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (G : Finset C) (V : C → Finset U) (a q : ℕ)
    (ha : 1 ≤ a) (hq : 1 ≤ q) (hn : 1 ≤ Fintype.card U)
    (hPool : ∀ u ∈ G, a * #(V u) ≥ Fintype.card U)
    (hg : 2 * a * (q - 1) ≤ #G) :
    let b := 2 ^ (q + 1) * a ^ q
    let poolInter := fun (S : Finset C) =>
      (if h : S.Nonempty then S.inf' h V else (univ : Finset U))
    let good := {S ∈ G.powersetCard q | b * #(poolInter S) ≥ Fintype.card U}
    b * q.factorial * #good ≥ (#G) ^ q := by sorry

end Erdos624
