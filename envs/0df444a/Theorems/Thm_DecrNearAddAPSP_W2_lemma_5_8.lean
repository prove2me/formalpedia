-- Prove2me | Theorems.Thm_DecrNearAddAPSP_W2_lemma_5_8
-- name    : DecrNearAddAPSP.W2.lemma_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:16:35.782896+00:00
-- url     : https://prove2.me/theorems/282e0bdb-d4ab-4758-bdf8-ea24973e8a83
-- title:
--   Lemma 5.8 — Algorithm 3 at every time t: d[u, v] ≤ w(P) + 2W₂(P) for every path of weight ≤ τ
-- statement:
--   Run Algorithm 3 with any depth $\tau\in\mathbb N$ on a decremental instance (integer weights in $[1,W]$, edge deletions and weight increases), for any sampled set $S\subseteq V$ and any valid pivot selector. Let $P_{u,v}$ be a path between $u$ and $v$ in $G$ at time $t\ge0$ (with $t$ at most the number of updates) with weight $w_t(P_{u,v})\le\tau$. Then
--   $$
--   d_t[u,v]\ \le\ w_t(P_{u,v})+2W_{2,t}(P_{u,v}).
--   $$
--
--   The bound holds for every surviving path, not only for shortest paths, because the right-hand side for shortest paths can decrease over time while the estimates of a decremental structure cannot. Specialized to shortest paths it is the $+2W_2$ guarantee of Algorithm 3 up to depth $\tau$.
--
--   Differences from the source:
--
--   - reading: Algorithm 3 (p. 29) and its description (pp. 28–31) → the process Alg3: pivot tree to depth 2τ, pivot ES-trees from S, E^τ_S read dynamically, aux weights max_{r≤t} L_{p_r(y),r}(u), edges Q, {u}×S̃, {u}×V directed away from u, monotone levels of F(u) then F̂(u), d = min{ℓ̂_u(v), ℓ̂_v(u)}; reason: the algorithm box leaves these details to the prose; each choice is the one the prose and the proof use (see the Alg3 definition)
--   - reading: S = sample(V, q); p(u) with ties arbitrary → every S ⊆ V and every valid pivot selector; reason: the lemma is a deterministic statement about every outcome of the sample and every tie-breaking
--   - reading: a weighted graph undergoing edge deletions (and weight increases, §2 p. 7) → a decremental instance: integer weights in [1, W], legal deletions and strict weight increases, for every W; reason: the decremental setting of p. 7, with the positive integer weights of §5 and p. 6
--   - reading: a path P_{u,v} in G at time t ≥ 0; d[u, v] → P a simple path (IsPath walk) of G_t with t ≤ |σ|, weights w_t and W_{2,t}; d_t[u, v] the estimate at time t; reason: §2: weights and W_i are taken at time t; times beyond the last update add nothing
--   - encoding: V ∪ S̃, weights and estimates → Fin n ⊕ Fin n; weights and d in ℕ∞; reason: Lean convention; same instances
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), p. 32, Lemma 5.8

import Mathlib
import Definitions.Def_DecrNearAddAPSP_W2_Graphs
import Definitions.Def_DecrNearAddAPSP_W2_Dynamic
import Definitions.Def_DecrNearAddAPSP_W2_MonoES
import Definitions.Def_DecrNearAddAPSP_W2_Alg3

namespace DecrNearAddAPSP.W2

/-- **Lemma 5.8** (p. 32). Run Algorithm 3 on a decremental instance (integer weights in `[1, W]`,
edge deletions and weight increases) with any depth `τ`, any sampled set `S` and any valid pivot
selector. Let `P_{u,v}` be a path between `u` and `v` in `G` at time `t ≥ 0` with weight
`w_t(P_{u,v}) ≤ τ`. Then `d_t[u, v] ≤ w_t(P_{u,v}) + 2W_{2,t}(P_{u,v})`. -/
theorem lemma_5_8 {n W : ℕ} (A : Alg3 n) (hinst : IsDecrInstance W A.G₀ A.σ)
    (hpiv : A.ValidPivots) (t : ℕ) (ht : t ≤ A.σ.length) (u v : Fin n)
    (P : (A.G t).adj.Walk u v) (hP : P.IsPath) (hw : (A.G t).walkWeight P ≤ A.τ) :
    A.est t u v ≤ (((A.G t).walkWeight P + 2 * (A.G t).heavy P 2 : ℕ) : ℕ∞) := by sorry

end DecrNearAddAPSP.W2
