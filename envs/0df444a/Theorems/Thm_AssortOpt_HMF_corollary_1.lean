-- Prove2me | Theorems.Thm_AssortOpt_HMF_corollary_1
-- name    : AssortOpt.HMF.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:19.643934+00:00
-- url     : https://prove2.me/theorems/35947d6f-5e26-4cad-9022-b10a903ef098
-- title:
--   Corollary 1, p. 20 — S-adjusted prices are monotone over tiers: r^S(ρ) ≤ r^S(ρ′) for ρ in a higher tier, or in the same tier with a different set
-- statement:
--   Suppose the list distribution has history-monotone futures and prices $r_j \ge 0$. Fix an assortment $S$ and $j \notin S$, and a partition of the realizable $S$-disjoint prefixes with endpoint $j$ into tiers $\mathcal T(1), \dots, \mathcal T(T)$ as in Lemma 2. For $\rho \in \mathcal T(t)$ and $\rho' \in \mathcal T(t')$,
--   $$r^S(\rho) \le r^S(\rho')$$
--   whenever either $t > t'$, or $t = t'$ and $\rho \ne \rho'$ as sets.
--
--   Prefixes with larger histories have better futures under $S$, hence smaller adjusted prices: stopping on them is less valuable. This monotonicity is what lets the proof of Theorem 2 add a 1-entry to a policy without losing revenue.
--
--   Differences from the source:
--   - encoding: items $\{1,\dots,n\}$, lists, support $\mathcal L$ with weights $p$ → `Fin n` (0-based), `ListDist` (finite support of `Nodup` lists, $p > 0$ on $\mathcal L$, $\sum p = 1$); reason: same instances.
--   - reading: "the partitioning … into tiers" (of Lemma 2) → every labelling $\tau$ satisfying Lemma 2's properties 1–2 (`IsTierPartition`); reason: Lemma 2 characterizes its partition only through these properties.
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 20, Corollary 1

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting

namespace AssortOpt.HMF

theorem corollary_1 {n : ℕ} (D : ListDist n) (hD : HasHistoryMonotoneFutures D)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S)
    (T : ℕ) (τ : List (Fin n) → ℕ) (hτ : IsTierPartition D S j T τ) :
    ∀ ρ ∈ tierDomain D S j, ∀ ρ' ∈ tierDomain D S j,
      (τ ρ' < τ ρ ∨ (τ ρ = τ ρ' ∧ ρ.toFinset ≠ ρ'.toFinset)) →
      adjPrice D r S ρ ≤ adjPrice D r S ρ' := by sorry

end AssortOpt.HMF
