-- Prove2me | Theorems.Thm_EvenCycleListing723_Main_lemma_3_2
-- name    : EvenCycleListing723.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:14.471952+00:00
-- url     : https://prove2.me/theorems/3c9cce63-a2c3-46f1-891c-0fcd5acf0fc1
-- title:
--   Lemma 3.2 — degree-weighted nearby pairs
-- statement:
--   Fix an integer $k\ge2$. Let $H$ be a finite simple undirected graph on $m\le n$ vertices, let $D\ge2$ be real, and assume every degree in $H$ is at most $2D$. Let $P$ be any set of ordered vertex pairs $(u,v)$ with $\deg_H(v)\ge D$ and $\operatorname{dist}_H(u,v)\le k-1$. With $\alpha_k=2^{-6k}(2k)^{-(2k-2)}$ and $S_k=\sum_{h=1}^{k-1}2^{h+2}=2^{k+2}-8$,
--
--   $$\sum_{(u,v)\in P}\deg_H(u)\ \le\ 2(1+512k^2S_k)n^2+\frac{16k^2S_k}{\alpha_k}\,t_{2k}(H).$$
--
--   The coefficients depend only on $k$, uniformly in $n,H,D,P$, and incur no logarithmic loss. Diagonal pairs are allowed, the second coordinate satisfies the degree threshold, and the first coordinate's degree is summed. No minimum degree, bipartiteness, or connectivity assumption is imposed on $H$. This controls exploration within a degree bucket.
--
--   **Formalization Note** The displayed coefficients instantiate the source's $O_k$: pp.6–8 bound the heavy contribution by $(8k^2/\alpha_k)t$, the light contribution by $512k^2n^2$, and the distance-$h$ partition loss by $2^{h+2}$. The distance-zero term contributes at most $n^2$ before the final factor two.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → SimpleGraph (Fin n), or Fin m with m ≤ n; reason: every finite vertex set can be relabeled; SimpleGraph imposes precisely simplicity and undirectedness
--   - encoding: unoriented noninduced cycle copies → edge sets of simple closed walks, with canonical dihedral vertex lists for output; reason: rotation and reversal identify the same copy; different cyclic edge orders remain distinct and chords are allowed
--   - encoding: distance at most k−1 → membership in the (k−1)-step BFS ball; reason: bounded reachability includes diagonal pairs and excludes disconnected pairs
--   - reading: O_k(n²+t) in the conclusion → 2(1+512k² S_k)n²+(16k² S_k/α_k)t, where S_k=Σ_{h=1}^{k−1}2^{h+2}; reason: pp.6–8 give heavy cost at most (8k²/α_k)t, light cost at most 512k²n², partition loss 2^{h+2}, diagonal cost at most n², and final factor 2
-- source:
--   Neha Pant and Virginia Vassilevska Williams, Listing Even Cycles Even Faster, STOC 2027 submission #723 (October 2026), p.5, Lemma 3.2; coefficient extraction from proof on pp.6–8; canonical PDF https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/723.pdf (SHA256 653ba349d1e9c1a87fe327137dddf959c6871a48cf5a052e91a47e341e9e9d8f)

import Mathlib
import Definitions.Def_EvenCycleListing723_Main_GraphModel

set_option autoImplicit false

namespace EvenCycleListing723.Main

open scoped BigOperators

/-- Lemma 3.2, p.5, with coefficients derived from pp.6–8; the first coordinate is summed. -/
theorem lemma_3_2 (k : ℕ) (hk : 2 ≤ k) (n m : ℕ) (hmn : m ≤ n)
    (H : SimpleGraph (Fin m)) (D : ℝ) (hD : 2 ≤ D)
    (hmax : ∀ v, (degree H v : ℝ) ≤ 2 * D)
    (P : Finset (Fin m × Fin m))
    (hP : ∀ p ∈ P, D ≤ (degree H p.2 : ℝ) ∧
      p.2 ∈ ball H Finset.univ p.1 (k - 1)) :
    (∑ p ∈ P, (degree H p.1 : ℝ)) ≤
      pairQuadraticCoefficient k * (n : ℝ) ^ 2 +
        pairCycleCoefficient k * (cycleCount H k : ℝ) := by sorry

end EvenCycleListing723.Main
