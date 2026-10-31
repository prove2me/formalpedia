-- Prove2me | Theorems.Thm_FairShares_pickShare_is_bundle_value
-- name    : FairShares.pickShare_is_bundle_value
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:04.336384+00:00
-- url     : https://prove2.me/theorems/501592e8-72d4-431b-a95a-1b8db523054a
-- title:
--   §4.1: the $\omega$-Picking-Order share is the value of a bundle and equals its share guarantee
-- statement:
--   Let $n\ge1$, let $\omega$ be a picking order for $m$ goods and $n$ agents, and let $v$ be any valuation. Then
--
--   1. there is a bundle $S$ with $v(S)$ equal to the $\omega$-Picking-Order share of $v$;
--   2. the share guarantee of the $\omega$-Picking-Order share at $v$ equals the share itself:
--   $$
--   \hat s(v,n)=\min_{k\in[n]}x_k .
--   $$
--
--   This is used in the proof of Lemma 14 (the implied guarantee for the true report is the share).
--
--   Differences from the source:
--   - generalization: valuations over goods → any function v : Finset (Fin m) → ℝ; reason: both clauses hold for every real set function; valuations over goods are among them
--   - encoding: a set M of m items, agents [n], a picking order ω1, …, ωm with ωj ∈ [n] → items Fin m, agents Fin n numbered from 0, ω : Fin m → Fin n, with 1 ≤ n; reason: name independence makes the naming of items and agents irrelevant; the list of pickers has length m, so every item is picked
--   - encoding: x_k, the maximum value agent k can ensure against an adversary making all other picks → gameVal: the backward-induction (max at k's picks, min at the adversary's) value of k's final bundle, started from all items with List.ofFn ω; reason: the game is finite with perfect information, so the max over agent strategies of the min over adversary strategies is the backward-induction value; same number
--   - encoding: the minimum over acceptable bundles (share guarantee ŝ, implied guarantee ŝ_v(v′)) → Finset.inf in WithTop ℝ over the bundles S with s(v′) ≤ v′(S); reason: for a realizable share the family is nonempty and the value is the real minimum; ⊤ only on an empty family, where the source's minimum is undefined
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, §4.1, p.15 ("Note that as these shares are defined to be a value of some bundle, for each picking order ω the share guarantee is the same as the share itself.")

import Mathlib
import Definitions.Def_FairShares_pickShare
import Definitions.Def_FairShares_shareGuarantee

namespace FairShares

/-- **The ω-Picking-Order share is the value of a bundle, so it equals its share guarantee.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, §4.1, p.15: "Note that as these shares are defined to be a value of some bundle, for each
picking order ω the share guarantee is the same as the share itself."

For `n ≥ 1` agents, every picking order `ω : Fin m → Fin n` and every valuation `v`:
1. some bundle `S` has `v S = pickShare ω v`;
2. the share guarantee `ŝ(v, n)` of the share `pickShare ω` equals `pickShare ω v`.

**Formalization Note.** No property of `v` is assumed. The share guarantee is a minimum in
`WithTop ℝ` (`FairShares.shareGuarantee`); clause 2 says it is the real number `pickShare ω v`. -/
theorem pickShare_is_bundle_value {m n : ℕ} (hn : 1 ≤ n) (ω : Fin m → Fin n)
    (v : Finset (Fin m) → ℝ) :
    (∃ S : Finset (Fin m), v S = pickShare ω v) ∧
      shareGuarantee (pickShare ω) v = ((pickShare ω v : ℝ) : WithTop ℝ) := by sorry

end FairShares
