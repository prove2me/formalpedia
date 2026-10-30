-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_lemma_11_connection
-- name    : APrioriTSP.Sampling.lemma_11_connection
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-29T14:39:59.766761+00:00
-- url     : https://prove2.me/theorems/50c50adb-37c8-4f3f-aa70-9cfb9b7a41c5
-- title:
--   Proof of Lemma 11, p. 9 — expected connection cost under σp-sampling is at most σ²p Σ (1 − σp)^{k−1} Σ min{C_i, C_{k−i}}
-- statement:
--   Let $(V,c,p)$ be a $p$-normalized a priori TSP instance with depot $d$ and $0<p<1$, i.e. $p(d)=1$ and $p(v)=p$ for every customer $v\ne d$. Let $0<\sigma<1$, and let $T^*=(v_0=d,v_1,\dots,v_{n-1})$ be a tour starting at the depot, with $v_j:=d$ for $j<0$ or $j>n-1$ and hop sums
--   $$C_k=p^2\sum_{j\in\mathbb Z}c(v_j,v_{j+k})\qquad(k\ge1).$$
--   Sample $S\subseteq V$ by including every customer independently with probability $\sigma p$ and the depot with probability $1$. Then the expected connection cost of the active customers satisfies
--   $$\mathbb E_S\Big[\sum_{v\in V}p(v)\,c(v,S)\Big]\ \le\ \sigma^2p\sum_{k=1}^\infty(1-\sigma p)^{k-1}\sum_{i=1}^{k-1}\min\{C_i,C_{k-i}\}.$$
--
--   This is the bound on the connection cost in the proof of Lemma 11 (p. 9): "we can bound the expected cost of connecting all active customers to the master tour by $2\sigma^2p\sum_{k\ge1}(1-\sigma p)^{k-1}\sum_{i=1}^{k-1}\min\{C_i,C_{k-i}\}$" (the cost of connecting active customer $v$ is $2c(v,S)$). Together with Proposition 10 for the master tour, it shows that (5) bounds the expected cost of the sampling algorithm with $f(p)=\sigma p$.
--
--   **Formalization Note** The sampling probabilities are `linSampling σ (p v)` ($=\sigma p$ for customers since $p<1$, and $=1$ for the depot); $c(v,S)$ is `distToSet c v S`; $C_k$ is `hopC c p d T k`. The outer sum is shifted $k\mapsto k+1$, so it reads $\sum_{k\ge0}(1-\sigma p)^k\sum_{i=1}^{k}\min\{C_i,C_{k+1-i}\}$.
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 9, proof of Lemma 11 (displayed bound on the expected cost of connecting all active customers to the master tour)

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

namespace APrioriTSP.Sampling

/-- p. 9 (proof of Lemma 11): on a `p`-normalized instance, sampling every customer with
probability `σ p` (and the depot), the expected connection cost `E[Σ_v p(v) c(v, S)]` is at most
`σ² p Σ_{k≥1} (1 − σp)^{k−1} Σ_{i=1}^{k−1} min {C_i, C_{k−i}}` for the hop sums `C` of any tour
starting at the depot (index shifted `k ↦ k + 1`). -/
theorem lemma_11_connection {V : Type} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (pf : V → ℝ) (d : V) (σ p : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hp0 : 0 < p) (hp1 : p < 1) (hnorm : IsNormalized c pf d p)
    (T : List V) (hT : IsTour T) (hd : T.head? = some d) :
    ∑ S : Finset V, subsetProb (fun v => linSampling σ (pf v)) S *
        ∑ v, pf v * distToSet c v S ≤
      σ ^ 2 * p * ∑' k : ℕ, (1 - σ * p) ^ k *
        ∑ i ∈ Finset.Icc 1 k, min (hopC c p d T i) (hopC c p d T (k + 1 - i)) := by
  sorry

end APrioriTSP.Sampling
