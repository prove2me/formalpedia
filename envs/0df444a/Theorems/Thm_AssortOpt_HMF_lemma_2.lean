-- Prove2me | Theorems.Thm_AssortOpt_HMF_lemma_2
-- name    : AssortOpt.HMF.lemma_2
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:27.051644+00:00
-- url     : https://prove2.me/theorems/d5bfe8fd-7d36-41c1-9fd0-f033dee8b6aa
-- title:
--   Lemma 2, p. 20 — under history-monotone futures the realizable S-disjoint prefixes ending in j split into tiers
-- statement:
--   Suppose the list distribution $\mathcal L, p$ has history-monotone futures. Fix an assortment $S$ and an item $j \notin S$, and consider the realizable prefixes $\rho$ with $\rho_{\mathrm{end}} = j$ and $\rho \cap S = \emptyset$. These prefixes can be partitioned into nonempty tiers $\mathcal T(1), \dots, \mathcal T(T)$ such that:
--
--   1. for tiers $t > t'$ and prefixes $\rho \in \mathcal T(t)$, $\rho' \in \mathcal T(t')$: $\rho \supsetneq \rho'$ as sets, and $\Pr[j' \succeq S_0 \mid \rho] \ge \Pr[j' \succeq S_0 \mid \rho']$ for all $j' \in S$;
--   2. within every tier $t$, either
--      (a) any two distinct prefixes $\rho, \rho' \in \mathcal T(t)$ satisfy $\rho \not\subseteq \rho'$ and $\rho' \not\subseteq \rho$ as sets and $\Pr[j' \succeq S_0 \mid \rho] = \Pr[j' \succeq S_0 \mid \rho']$ for all $j' \in S$; or
--      (b) all prefixes in $\mathcal T(t)$ are identical as sets.
--
--   The tiers order the prefixes ending in $j$ so that larger histories have larger futures; this is the structure that history-monotone futures imposes and that the extremal argument for Theorem 2 exploits.
--
--   **Formalization Note** A partition into tiers is a labelling $\tau$ of the prefixes by $\{1, \dots, T\}$ hitting every label (`IsTierPartition`). When there are no such prefixes, $T = 0$.
--
--   Differences from the source:
--   - encoding: items $\{1,\dots,n\}$, lists, support $\mathcal L$ with weights $p$ → `Fin n` (0-based), `ListDist` (finite support of `Nodup` lists, $p > 0$ on $\mathcal L$, $\sum p = 1$); reason: same instances.
--   - encoding: hypotheses "$S \subsetneq N$ and $j \notin S$" → only $j \notin S$; reason: $j \notin S$ implies $S \subsetneq N$.
--   - encoding: a partition into tiers $\mathcal T(1),\dots,\mathcal T(T)$ → a labelling $\tau$ onto $\{1,\dots,T\}$ (every label used); reason: the same partitions with nonempty, indexed parts.
--   - reading: "distinct prefixes" in 2(a) → distinct as lists; reason: prefixes are ordered lists; two distinct prefixes with equal sets are $\subseteq$-comparable and so belong to a tier of type (b), as in Example 6 (p. 43).
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 20, Lemma 2

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting

namespace AssortOpt.HMF

theorem lemma_2 {n : ℕ} (D : ListDist n) (hD : HasHistoryMonotoneFutures D)
    (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S) :
    ∃ (T : ℕ) (τ : List (Fin n) → ℕ), IsTierPartition D S j T τ := by sorry

end AssortOpt.HMF
