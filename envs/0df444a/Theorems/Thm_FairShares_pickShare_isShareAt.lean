-- Prove2me | Theorems.Thm_FairShares_pickShare_isShareAt
-- name    : FairShares.pickShare_isShareAt
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:13:59.855979+00:00
-- url     : https://prove2.me/theorems/0f5f5f55-e908-4d34-ba36-6442b0818cf8
-- title:
--   §4.1 (implicit in Proposition 5): the $\omega$-Picking-Order share is a share
-- statement:
--   Let $n\ge1$, let $\omega$ be a picking order for $m$ goods and $n$ agents, and let $D$ be any set of valuations on the bundles of the goods. Then the $\omega$-Picking-Order share satisfies Definition 2 on $D$:
--
--   1. **Realizability:** for every $v\in D$, $\min_k x_k\le \max_{S} v(S)$;
--   2. **Name independence:** renaming the goods by a permutation $\sigma$ (when the renamed valuation is in $D$) does not change the share.
--
--   The paper calls these functions shares (§4.1, Proposition 5) without separately checking Definition 2; the proof of Theorem 1 needs it, because the shares it dominates must be shares.
--
--   Differences from the source:
--   - reading: the ω-Picking-Order share is called a share (Definition 2) without proof → realizability and name independence stated as a theorem; reason: the paper presupposes it in §4.1 and Proposition 5, and Theorem 1's proof needs it
--   - generalization: a class C of valuations (normalized, non-decreasing, nonnegative set functions) → an arbitrary set D of functions Finset (Fin m) → ℝ; reason: the property is asserted for every set of real set functions; every class of valuations over goods on m items is such a set
--   - encoding: a set M of m items, agents [n], a picking order ω1, …, ωm with ωj ∈ [n] → items Fin m, agents Fin n numbered from 0, ω : Fin m → Fin n, with 1 ≤ n; reason: name independence makes the naming of items and agents irrelevant; the list of pickers has length m, so every item is picked
--   - encoding: x_k, the maximum value agent k can ensure against an adversary making all other picks → gameVal: the backward-induction (max at k's picks, min at the adversary's) value of k's final bundle, started from all items with List.ofFn ω; reason: the game is finite with perfect information, so the max over agent strategies of the min over adversary strategies is the backward-induction value; same number
--   - encoding: renaming the items → S ↦ v (σ S) for a permutation σ of Fin m, required when the renamed valuation is in D; reason: renamings of a set of m items are its permutations; the share is only constrained on the class
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, §4.1, p.15 ("we design a collection Q of shares, where every share in Q is feasible and self maximizing"); Proposition 5, p.16; Definition 2, p.9

import Mathlib
import Definitions.Def_FairShares_pickShare
import Definitions.Def_FairShares_IsShareAt

namespace FairShares

/-- **The ω-Picking-Order share is a share (realizable and name independent).**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, Proposition 5, p.16: "Fix any class C of valuations. For any picking order ω, the
ω-Picking-Order share is feasible and self maximizing for C." (Proposition 5 and the proof of
Theorem 1 treat it as a share in the sense of Definition 2, p.9.)

For `n ≥ 1` agents, every picking order `ω : Fin m → Fin n` and every set `D` of valuations on the
bundles of `Fin m`, `pickShare ω` satisfies Definition 2 on `D`: `pickShare ω v ≤ max_S v(S)` for
every `v ∈ D`, and renaming the items (when the renamed valuation is in `D`) does not change it.

**Formalization Note.** `D` is arbitrary; no property of the valuations is assumed. -/
theorem pickShare_isShareAt {m n : ℕ} (hn : 1 ≤ n) (ω : Fin m → Fin n)
    (D : Set (Finset (Fin m) → ℝ)) :
    IsShareAt D (pickShare ω) := by sorry

end FairShares
