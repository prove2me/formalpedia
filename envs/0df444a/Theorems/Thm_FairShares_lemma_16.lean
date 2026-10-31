-- Prove2me | Theorems.Thm_FairShares_lemma_16
-- name    : FairShares.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:14.861656+00:00
-- url     : https://prove2.me/theorems/3df4a7c3-7fdb-4f82-9b86-b58ced0bfc18
-- title:
--   Lemma 16: for additive $v$ some picking-order share equals $\mathrm{MMS}_n(v)$
-- statement:
--   Let $n\ge1$ and let $v$ be an additive valuation on $m$ goods. Then there is a picking order $\omega_v$ for $m$ goods and $n$ agents such that the $\omega_v$-Picking-Order share of $v$ equals the maximin share
--   $$
--   \mathrm{MMS}_n(v)=\max_{(A_1,\dots,A_n)}\ \min_{j\in[n]} v(A_j),
--   $$
--   the maximum over all partitions of the goods into $n$ possibly empty bundles.
--
--   This is the step that turns domination of all picking-order shares into domination of the MMS on additive valuations.
--
--   Differences from the source:
--   - encoding: a set M of m items, agents [n], a picking order ω1, …, ωm with ωj ∈ [n] → items Fin m, agents Fin n numbered from 0, ω : Fin m → Fin n, with 1 ≤ n; reason: name independence makes the naming of items and agents irrelevant; the list of pickers has length m, so every item is picked
--   - encoding: x_k, the maximum value agent k can ensure against an adversary making all other picks → gameVal: the backward-induction (max at k's picks, min at the adversary's) value of k's final bundle, started from all items with List.ofFn ω; reason: the game is finite with perfect information, so the max over agent strategies of the min over adversary strategies is the backward-induction value; same number
--   - encoding: MMSₙ(v), Definition 1 → the published LittleCharity.MMS.mms v n Finset.univ; reason: the supremum over all maps Fin m → Fin n of the minimum bundle value, i.e. Definition 1 for n ≥ 1
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, Lemma 16, p.35; Definition 1, p.9

import Mathlib
import Definitions.Def_FairShares_pickShare
import Definitions.Def_FairShares_IsAdditive
import Definitions.Def_LittleCharity_MMS_Setting

namespace FairShares

/-- **Lemma 16: for an additive valuation some picking-order share equals the MMS.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, Lemma 16, p.35: "Consider a setting with n agents and a set of items M. For any additive
valuation v there exists a picking order ωv for which the ωv-Picking-Order share for an agent with
valuation v equals to the MMS of that agent, that is, to MMSn(v)."

For `n ≥ 1` agents and every additive valuation `v` on the bundles of `Fin m` there is a picking
order `ω : Fin m → Fin n` with `pickShare ω v = MMS_n(v)`.

**Formalization Note.** `MMS_n(v)` is the published `LittleCharity.MMS.mms v n Finset.univ`, the
maximum over all maps `Fin m → Fin n` (partitions into `n` possibly empty bundles) of the
minimum bundle value: Definition 1, p.9. -/
theorem lemma_16 {m n : ℕ} (hn : 1 ≤ n) (v : Finset (Fin m) → ℝ) (hv : IsAdditive v) :
    ∃ ω : Fin m → Fin n, pickShare ω v = LittleCharity.MMS.mms v n Finset.univ := by sorry

end FairShares
