-- Prove2me | Theorems.Thm_DecrNearAddAPSP_W2_lemma_5_7
-- name    : DecrNearAddAPSP.W2.lemma_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:16:22.383111+00:00
-- url     : https://prove2.me/theorems/b1467239-72fb-462d-9c1e-b88bd8476835
-- title:
--   Lemma 5.7 — Algorithm 3 at time 0: every path of weight ≤ τ has an alternative in F̂(u) bounding d[u, v] by w(P) + 2W₂(P)
-- statement:
--   Run Algorithm 3 with any depth $\tau\in\mathbb N$ on a decremental instance with integer weights in $[1,W]$, for any sampled set $S\subseteq V$ and any valid pivot selector. Let $P_{u,v}$ be a path between $u$ and $v$ in $G$ at time $t=0$ with weight $w(P_{u,v})\le\tau$. Then there exists a path $P^*_{u,v}$ between $u$ and $v$ in $\hat F_0(u)$ such that
--   $$
--   d_0[u,v]\ \le\ w\big(P^*_{u,v}\big)\ \le\ w(P_{u,v})+2W_2(P_{u,v}).
--   $$
--
--   This is the base case of the induction (Lemma 5.8) that gives Algorithm 3 its local additive stretch $+2W_2$ up to depth $\tau$, the building block that §7 extends to unbounded distances.
--
--   Differences from the source:
--
--   - reading: Algorithm 3 (p. 29) and its description (pp. 28–31) → the process Alg3: pivot tree to depth 2τ, pivot ES-trees from S, E^τ_S read dynamically, aux weights max_{r≤t} L_{p_r(y),r}(u), edges Q, {u}×S̃, {u}×V directed away from u, monotone levels of F(u) then F̂(u), d = min{ℓ̂_u(v), ℓ̂_v(u)}; reason: the algorithm box leaves these details to the prose; each choice is the one the prose and the proof use (see the Alg3 definition)
--   - reading: S = sample(V, q); p(u) with ties arbitrary → every S ⊆ V and every valid pivot selector; reason: the lemma is a deterministic statement about every outcome of the sample and every tie-breaking
--   - reading: a weighted graph undergoing edge deletions (and weight increases, §2 p. 7) → a decremental instance: integer weights in [1, W], legal deletions and strict weight increases, for every W; reason: the decremental setting of p. 7, with the positive integer weights of §5 and p. 6
--   - reading: a path P_{u,v} in G at time 0; a path P*_{u,v} in F̂(u) → P a simple path (IsPath walk) of G_0; P* a list of distinct vertices of V ⊕ S̃ from u to v whose consecutive pairs are edges of F̂_0(u), weight the sum of their weights; reason: §7 (Lemma 7.1) says 'simple path'; a path in F̂(u) is a path of that directed graph
--   - encoding: V ∪ S̃, weights and estimates → Fin n ⊕ Fin n; weights and d in ℕ∞ (∞ = no edge); reason: Lean convention; same instances
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), p. 31, Lemma 5.7

import Mathlib
import Definitions.Def_DecrNearAddAPSP_W2_Graphs
import Definitions.Def_DecrNearAddAPSP_W2_Dynamic
import Definitions.Def_DecrNearAddAPSP_W2_MonoES
import Definitions.Def_DecrNearAddAPSP_W2_Alg3

namespace DecrNearAddAPSP.W2

/-- **Lemma 5.7** (p. 31). Run Algorithm 3 on a decremental instance (integer weights in `[1, W]`)
with any depth `τ`, any sampled set `S` and any valid pivot selector. Let `P_{u,v}` be a path between
`u` and `v` in `G` at time `t = 0` with weight `w(P_{u,v}) ≤ τ`. Then there is a path `P*_{u,v}`
between `u` and `v` in `F̂(u)` such that `d[u, v] ≤ w(P*_{u,v}) ≤ w(P_{u,v}) + 2W_2(P_{u,v})`. -/
theorem lemma_5_7 {n W : ℕ} (A : Alg3 n) (hinst : IsDecrInstance W A.G₀ A.σ)
    (hpiv : A.ValidPivots) (u v : Fin n) (P : (A.G 0).adj.Walk u v) (hP : P.IsPath)
    (hw : (A.G 0).walkWeight P ≤ A.τ) :
    ∃ Pstar : List (Fin n ⊕ Fin n), IsDPath (A.Fhat 0 u) (Sum.inl u) (Sum.inl v) Pstar ∧
      A.est 0 u v ≤ dWeight (A.Fhat 0 u) Pstar ∧
      dWeight (A.Fhat 0 u) Pstar ≤
        (((A.G 0).walkWeight P + 2 * (A.G 0).heavy P 2 : ℕ) : ℕ∞) := by sorry

end DecrNearAddAPSP.W2
