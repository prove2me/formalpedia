-- Prove2me | Theorems.Thm_CrowdLastMile_lemma_1
-- name    : CrowdLastMile.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:59.325101+00:00
-- url     : https://prove2.me/theorems/010dfaa8-317b-4e75-aa08-ec969b4149b0
-- title:
--   Lemma 1, p.12 — worst-case average opportunity cost of the cheapest $N$ drivers
-- statement:
--   Let $1\le N\le\mathbb N$, let $\mu^k_1,\dots,\mu^k_{\mathbb N}\ge0$ be the mean opportunity costs, $\sigma^k>0$ their common standard deviation, and $\gamma^k\ge0$ the level of conservatism. Let $U_K$ be the uncertainty set (6) with $\sigma^k_i=\sigma^k$. Then
--
--   $$
--   \min_{S\subseteq\{1,\dots,\mathbb N\},\,|S|=N}\ \max_{(K_1,\dots,K_{\mathbb N})\in U_K}\frac{\sum_{i\in S}K_i}{N}=\frac{\sum_{i=1}^{N}\mu^k_{(i)}+\gamma^k\sqrt N\sigma^k}{N},
--   $$
--
--   where $\mu^k_{(1)}\le\dots\le\mu^k_{(\mathbb N)}$ are the order statistics of the means. More precisely:
--
--   1. for each $S$ with $|S|=N$ the inner maximum is attained and equals $\big(\sum_{i\in S}\mu^k_i+\gamma^k\sigma^k\sqrt N\big)/N$;
--   2. the minimum over such $S$ of these maxima is attained and equals the right-hand side above.
--
--   This value is the worst-case average opportunity cost of the cheapest $N$ drivers, and it is the right-hand side of the participation constraint of Problem (14).
--
--   Differences from the source:
--   - encoding: the condition of U_K (6) ranges over all I ⊆ {1,…,ℕ} → it ranges over non-empty I; reason: at I = ∅ the printed quotient is 0/0
--   - encoding: min_S max_K (Σ_{i∈S} K_i)/N = (Σ_{i=1}^N μ^k_(i) + γ^k√N σ^k)/N → IsGreatest for each S with |S| = N, and IsLeast for the set of these maxima; reason: Lean has no min/max of a set of reals; attainment is what the printed min and max assert
--   - encoding: no explicit ranges in Lemma 1 → 1 ≤ N ≤ ℕ, σ^k > 0, γ^k ≥ 0, μ^k_i ≥ 0; reason: these are the model's standing facts; μ^k_i ≥ 0 is what makes the proof's maximizer K̂ nonnegative, so that U_K contains it
--   - encoding: order statistics μ^k_(1) ≤ … ≤ μ^k_(ℕ) → the first N entries of the sorted multiset of the means; reason: Lean convention; same value
-- source:
--   Fatehi–Wagner, Crowdsourcing Last-Mile Deliveries, SSRN 3434625, Lemma 1, p.12; proof, p.34

import Mathlib
import Definitions.Def_CrowdLastMile_sumCheapest
import Definitions.Def_CrowdLastMile_UK

namespace CrowdLastMile

/-- **Lemma 1**, p.12 (Fatehi–Wagner, Crowdsourcing Last-Mile Deliveries, SSRN 3434625), with the
assumption `σ^k_i = σ^k` of p.11. For every `S ⊆ {1, …, ℕ}` with `|S| = N`, the maximum of
`(∑_{i∈S} K_i)/N` over `U_K` is attained and equals `(∑_{i∈S} μ^k_i + γ^k σ^k √N)/N`; the minimum over
such `S` of these maxima is attained and equals `(∑_{i=1}^N μ^k_(i) + γ^k √N σ^k)/N`.

**Formalization Note.** The `min max` of the paper is stated with `IsGreatest` and `IsLeast`, so
that attainment is part of the statement. -/
theorem lemma_1 {pop : ℕ} (N : ℕ) (hN : 1 ≤ N) (hpop : N ≤ pop)
    (μk : Fin pop → ℝ) (σk γk : ℝ) (hμ : ∀ i, 0 ≤ μk i) (hσ : 0 < σk) (hγ : 0 ≤ γk) :
    (∀ S : Finset (Fin pop), S.card = N →
      IsGreatest (subsetAverages μk (fun _ => σk) γk N S)
        (((∑ i ∈ S, μk i) + γk * σk * Real.sqrt (N : ℝ)) / (N : ℝ))) ∧
    IsLeast
      {x | ∃ S : Finset (Fin pop), S.card = N ∧
        IsGreatest (subsetAverages μk (fun _ => σk) γk N S) x}
      ((sumCheapest μk N + γk * Real.sqrt (N : ℝ) * σk) / (N : ℝ)) := by sorry

end CrowdLastMile
