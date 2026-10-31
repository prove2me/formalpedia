-- Prove2me | Theorems.Thm_FairShares_lemma_14
-- name    : FairShares.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:47.95723+00:00
-- url     : https://prove2.me/theorems/bd7cd053-1b01-4c9f-bd56-759fcec03acb
-- title:
--   Lemma 14: every picking-order share is self-maximizing
-- statement:
--   Let $n\ge1$, let $\omega$ be a picking order for $m$ goods and $n$ agents, and let $D$ be any set of valuations on the bundles of the goods. Then the $\omega$-Picking-Order share is self-maximizing on $D$: for every true valuation $v\in D$ and every report $v'\in D$,
--   $$
--   \hat s(v,n)\ \ge\ \hat s_v(v') .
--   $$
--
--   Together with Lemma 15 this gives the first sentence of Proposition 5.
--
--   Differences from the source:
--   - generalization: a class C of valuations (normalized, non-decreasing, nonnegative set functions) → an arbitrary set D of functions Finset (Fin m) → ℝ; reason: the property is asserted for every set of real set functions; every class of valuations over goods on m items is such a set
--   - encoding: a set M of m items, agents [n], a picking order ω1, …, ωm with ωj ∈ [n] → items Fin m, agents Fin n numbered from 0, ω : Fin m → Fin n, with 1 ≤ n; reason: name independence makes the naming of items and agents irrelevant; the list of pickers has length m, so every item is picked
--   - encoding: x_k, the maximum value agent k can ensure against an adversary making all other picks → gameVal: the backward-induction (max at k's picks, min at the adversary's) value of k's final bundle, started from all items with List.ofFn ω; reason: the game is finite with perfect information, so the max over agent strategies of the min over adversary strategies is the backward-induction value; same number
--   - encoding: the minimum over acceptable bundles (share guarantee ŝ, implied guarantee ŝ_v(v′)) → Finset.inf in WithTop ℝ over the bundles S with s(v′) ≤ v′(S); reason: for a realizable share the family is nonempty and the value is the real minimum; ⊤ only on an empty family, where the source's minimum is undefined
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, Lemma 14, p.34

import Mathlib
import Definitions.Def_FairShares_pickShare
import Definitions.Def_FairShares_SelfMaxAt

namespace FairShares

/-- **Lemma 14: every picking-order share is self-maximizing.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, Lemma 14, p.34: "Fix any class C of valuations. For any picking order ω, the
ω-Picking-Order share is self maximizing for C."

For `n ≥ 1` agents, every picking order `ω : Fin m → Fin n` and every set `D` of valuations on the
bundles of `Fin m`: for all `v, v' ∈ D`, the implied guarantee `ŝ_v(v')` of `pickShare ω` is at most
its share guarantee `ŝ(v, n)`.

**Formalization Note.** `D` is an arbitrary set of real functions on bundles (the paper's
valuations are normalized and non-decreasing). -/
theorem lemma_14 {m n : ℕ} (hn : 1 ≤ n) (ω : Fin m → Fin n) (D : Set (Finset (Fin m) → ℝ)) :
    SelfMaxAt D (pickShare ω) := by sorry

end FairShares
