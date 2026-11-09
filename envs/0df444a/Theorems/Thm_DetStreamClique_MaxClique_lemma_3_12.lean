-- Prove2me | Theorems.Thm_DetStreamClique_MaxClique_lemma_3_12
-- name    : DetStreamClique.MaxClique.lemma_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:17.38905+00:00
-- url     : https://prove2.me/theorems/ad08f16d-225c-4eea-8ffd-17d648fd6460
-- title:
--   Lemma 3.12 — information at a minimizing gadget
-- statement:
--   For any nonempty block family of the hard distribution, fix a base graph $g$ and a message $m$ in the range of Alice's message map. Put $J_i=J(A_i\mid M=m,G_0=g)$ and let $i_*$ minimize these values. Then
--   $$\ell J_{i_*}\le\sum_i J_i\le J(A\mid M=m,G_0=g).$$
--   Together with the uniform packing lower bound, these inequalities imply $J_{i_*}=o(b)$ whenever the joint information is $o(n^2/b)$. A minimizing index is constructed from the data, with unrestricted tie breaking.
--
--   Differences from the source:
--   - encoding: blocks have size 18b and sampled subsets size 9b with b ≥ 1 → k=9b is a natural number with k ≥ 9, and block size is 2k; reason: these cardinalities require 9b integral and this parametrization covers exactly those instances; k is not the goal approximation ratio
--   - generalization: the blocks supplied by Lemma 3.10 → every block family with the same cardinalities and pairwise intersections at most one; reason: the proof uses precisely these properties, so the family supplied by Lemma 3.10 is included
--   - encoding: conditional distributions at realized messages and background values → positive conditioning events or nonempty message fibers; reason: realized finite-law values have positive probability; undefined null conditionings are excluded
--   - encoding: conditioning on the realized base graph → the uniform tuple law at a fixed base graph; reason: the tuple is independent of the base graph and each graph has positive uniform mass
--   - reading: joint information o(n²/b) implies minimum-coordinate information o(b) → the two finite inequalities in the printed proof, before its asymptotic substitution; reason: with ℓ≥c n²/b² they imply the printed implication for every family
--   - encoding: argmin over the block indices → a chosen minimizing index for ℓ>0; reason: the packing has positive ℓ in its nondegenerate range; minimization is undefined for an empty family
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, Lemma 3.12, p. 17

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_HardInstance

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique

/-- Lemma 3.12, p. 17: explicit inequalities used before its asymptotic conclusion. -/
theorem lemma_3_12 {n ℓ k : ℕ} [NeZero ℓ]
    (B : BlockSystem n ℓ k) (hk : 9 ≤ k) {M : Type} [Fintype M]
    (π : OneWayProtocol (Graph n) (Graph n) M (Finset (Fin n)))
    (G : Graph n) (m : M) (hm : (fiber B π G m).Nonempty) :
    (ℓ : ℝ) * coordinateInfo B π G m (minIndex B π G m) ≤
      ∑ i, coordinateInfo B π G m i ∧
    (∑ i, coordinateInfo B π G m i) ≤ jointInfo B π G m := by sorry

end DetStreamClique.MaxClique
