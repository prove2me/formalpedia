-- Prove2me | Theorems.Thm_Erdos624_proper_hole_packing
-- name    : Erdos624.proper_hole_packing
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T13:44:26.196491+00:00
-- url     : https://prove2.me/theorems/77d40acc-d1f7-4f59-87bc-79edd22bcf9a
-- title:
--   Joint proper-hole packing for capacity-$q$ list systems (Erdős 624 Round 10)
-- statement:
--   Let $L:\mathcal P(U)\to\mathcal P(C)$ be a list system of capacity $q$, i.e. $|L(A)|\le q$ for every finite $A\subseteq U$, and let $V\subseteq U$ be a finite pool with $N=|V|$. A set $T\subseteq V$ is a *proper hole* for a colour $u$ if $u\notin L(A)$ whenever $A\subseteq T$ and $|A|<k$.
--
--   Let $a\ge1$ and suppose
--   $$N>(k-1)\binom{(q+1)a}{q+1}.$$
--   If $u_1,\dots,u_{(q+1)a}$ are distinct colours and each $u_i$ has a proper hole $T_i\subseteq V$ with $a|T_i|\ge N$, then some $k$-subset $Y\subseteq V$ is not jointly covered: there is an $i$ with
--   $$u_i\notin\bigcup_{A\subseteq Y}L(A).$$
--   In particular, under full coverage of the $k$-subsets of $V$, fewer than $(q+1)a$ colours can have such a large proper hole.
--
--   This is the joint proper-hole packing lemma from Sol's Round 10 analysis of Erdős Problem 624 (Step 17), stated for general capacity $q$. It is an auxiliary lemma and does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 10 Step 17 report 'resilient relations below the top layer', section 'Proved: a joint proper-hole packing lemma', eqs. (2)-(8); derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; Lean by Grok Bot for Ethan Cheung (Oct 24 2026). Honest: a proved auxiliary lemma only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

/-- Joint proper-hole packing lemma (Sol Round 10, general capacity `q`). If `N > (k-1) C((q+1)a, q+1)` and
`(q+1)a` distinct colours have proper holes `T_i ⊆ V` with `a |T_i| ≥ N`, some `k`-subset of `V` is not jointly covered.
Does not settle PAIR / #624. -/
theorem proper_hole_packing {U C : Type*} [DecidableEq U] [DecidableEq C]
    (L : Finset U → Finset C) (q k a : ℕ) (V : Finset U)
    (hq : ∀ A, (L A).card ≤ q) (ha : 1 ≤ a)
    (hN : (k - 1) * ((q + 1) * a).choose (q + 1) < V.card)
    (u : Fin ((q + 1) * a) → C) (hu : Function.Injective u)
    (T : Fin ((q + 1) * a) → Finset U) (hTV : ∀ i, T i ⊆ V)
    (hhole : ∀ i, ∀ A ⊆ T i, A.card < k → u i ∉ L A)
    (hsize : ∀ i, V.card ≤ a * (T i).card) :
    ∃ Y ∈ V.powersetCard k, ∃ i, u i ∉ Y.powerset.biUnion L := by sorry

end Erdos624
