-- Prove2me | Theorems.Thm_FairShares_lemma_15
-- name    : FairShares.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:00.808357+00:00
-- url     : https://prove2.me/theorems/435e619f-d2e6-4fae-9207-d7621b04234f
-- title:
--   Lemma 15 (first sentence): every picking-order share is feasible
-- statement:
--   Let $n\ge1$, let $\omega$ be a picking order for $m$ goods and $n$ agents, and let $D$ be any set of valuations on the bundles of the goods. Then the $\omega$-Picking-Order share is feasible on $D$: for every profile $(v_0,\dots,v_{n-1})$ of valuations in $D$ there is an allocation $A$ with
--   $$
--   v_i(A_i)\ \ge\ \min_{k\in[n]}x_k(v_i)\qquad\text{for every agent } i .
--   $$
--
--   This item is the first sentence of Lemma 15. The second sentence (an acceptable allocation is computable in polynomial time for additive valuations) is not part of this mission.
--
--   Differences from the source:
--   - generalization: a class C of valuations (normalized, non-decreasing, nonnegative set functions) → an arbitrary set D of functions Finset (Fin m) → ℝ; reason: the property is asserted for every set of real set functions; every class of valuations over goods on m items is such a set
--   - encoding: a set M of m items, agents [n], a picking order ω1, …, ωm with ωj ∈ [n] → items Fin m, agents Fin n numbered from 0, ω : Fin m → Fin n, with 1 ≤ n; reason: name independence makes the naming of items and agents irrelevant; the list of pickers has length m, so every item is picked
--   - encoding: x_k, the maximum value agent k can ensure against an adversary making all other picks → gameVal: the backward-induction (max at k's picks, min at the adversary's) value of k's final bundle, started from all items with List.ofFn ω; reason: the game is finite with perfect information, so the max over agent strategies of the min over adversary strategies is the backward-induction value; same number
--   - encoding: an allocation (partition into n possibly empty bundles) → A : Fin m → Fin n, agent i's bundle A⁻¹(i); reason: maps to Fin n are exactly the labelled partitions into n possibly empty bundles
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, Lemma 15, first sentence, p.34

import Mathlib
import Definitions.Def_FairShares_pickShare
import Definitions.Def_FairShares_FeasibleAt

namespace FairShares

/-- **Lemma 15 (first sentence): every picking-order share is feasible.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, Lemma 15, p.34: "Fix any class C of valuations. For any picking order ω, the
ω-Picking-Order share is feasible for C."

For `n ≥ 1` agents, every picking order `ω : Fin m → Fin n` and every set `D` of valuations: for
every profile `vs : Fin n → _` of valuations in `D` there is an allocation `A : Fin m → Fin n` giving
every agent `i` a bundle with `pickShare ω (vs i) ≤ vs i (A⁻¹ i)`.

**Formalization Note.** The lemma's second sentence (polynomial-time computation for additive
valuations) is not formalized. `D` is arbitrary. -/
theorem lemma_15 {m n : ℕ} (hn : 1 ≤ n) (ω : Fin m → Fin n) (D : Set (Finset (Fin m) → ℝ)) :
    FeasibleAt n D (pickShare ω) := by sorry

end FairShares
