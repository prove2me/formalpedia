-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_lemma_3_4
-- name    : FasterDistributedMatching.ApproximateMatching.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:11:04.794687+00:00
-- url     : https://prove2.me/theorems/77402410-06be-4f76-ac7e-d3dd1456dac9
-- title:
--   Lemma 3.4 — randomized cut cost
-- statement:
--   Let $x$ be any nonnegative edge assignment on a finite simple graph, let $q>0$, let $\ell\ge2$ be an integer, and form its locally paired active-edge graph and valid short-block partition. Choose one copy uniformly from each block, with pairwise independence between distinct blocks. Let $c_v,W,Q$ be the physical loads, total weight and quadratic penalty, and let $k_v$ count selected copies created by $v$ and $r_v=d_v\bmod2$ count true endpoints. Then
--
--   $$\mathbb E\!\left[2q^2\sum_v(2k_v+r_v)^2\right]\le\frac{4Q}{\ell^2}+36qW.$$
--
--   No upper load bound or fractional feasibility is assumed. A block may contain several copies of one creator. The law can be any real probability distribution with the specified one- and two-block marginals.
--
--   This is the quadratic cut-loss estimate, including the true-endpoint contribution.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs → SimpleGraph (Fin N), with arbitrary supplied bounds n and degree; reason: every finite simple graph can be relabelled in this way; the carrier index is never processor input
--   - encoding: edge assignments → real functions on unordered pairs, zero off actual edges; reason: zero extension represents exactly the source edge values
--   - generalization: virtual graphs arising in the bipartite matching section → locally paired active edges of an arbitrary finite simple graph; reason: the block, cut expectation and cut derandomization statements use degree at most two and local creator counts, not the parity of cycles; bipartite stages are included
--   - encoding: uniform cuts with pairwise independence between blocks → arbitrary normalized nonnegative finite joint masses with exact uniform one-block and product two-block marginals; reason: every joint law of finitely many finite labels has this representation; nonleader coordinates are ignored
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), Lemma 3.4, printed p.10, PDF p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Virtual

namespace FasterDistributedMatching.ApproximateMatching

/- Lemma 3.4, printed p.10 / PDF p.12. No load feasibility is assumed. -/
open Classical in
theorem lemma_3_4 (N : ℕ) (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ)
    (hx : NonnegativeAssignment G x) (q : ℝ) (hq : 0 < q) (ell : ℕ) (hell : 2 ≤ ell)
    (p : Pairing N) (hp : ValidPairing G x q p) (B : BlockAssignment p)
    (hB : ValidBlocks ell B) (mu : (Copy p → Copy p) → ℝ)
    (hmu : PairwiseUniformCuts B mu) :
    (∑ s, mu s * cutCost G x q B s) ≤
      4 * penalty G x / (ell : ℝ) ^ 2 + 36 * q * totalWeight G x := by sorry

end FasterDistributedMatching.ApproximateMatching
