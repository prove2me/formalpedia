-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_conditional_edge_entropy
-- name    : DistributedMIS.LocalLowerBound.conditional_edge_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:21.587296+00:00
-- url     : https://prove2.me/theorems/b274d53a-1b6f-4032-9054-3a1020887ebf
-- title:
--   Lemma 7.2 — Conditional edge entropy
-- statement:
--   Let Z be a symmetric radius-R rule on the infinite D-regular tree, with k coordinates. For adjacent u,v and 0≤t≤R, let F_t be the deduplicated union of the central matrix and both radius-t views. Write K=H(Z_v|N_R(v)). Then
--
--   $$\frac D2 H(Z_u,Z_v\mid F_t)\ge(D-1)H(Z_v\mid N_t(v))+K.$$
--
--   All entropies average over the specified conditioning law. This compares edge uncertainty with vertex uncertainty without a hidden-layer multiplier.
--
--   Differences from the source:
--   - encoding: the infinite D-regular tree with coordinates [k] and output 0 → a SimpleGraph on ℕ satisfying IsRegularTree, coordinates Fin k, and output Option (Fin k); reason: all countable regular trees are isomorphic; coordinate a is source a+1 and none is source 0; all graph automorphisms act, including rooted branch permutations
--   - encoding: finite conditional probabilities of independent fair edge matrices → exact uniform cylinder sums with transposed reverse orientations; reason: only the finitely many required edge variables are averaged; this is the marginal of the infinite fair product law, with arbitrary finite radius retained
--   - generalization: the large-degree application of the regular-tree model → all D≥2 and k≥1; reason: the structural entropy and symmetry statements need no logarithmic parameter regime; every source instance is included
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Lemma 7.2, printed/PDF pp. 19

import Definitions.Def_DistributedMIS_LocalLowerBound_Iteration

namespace DistributedMIS.LocalLowerBound

theorem conditional_edge_entropy (G : SimpleGraph ℕ) [G.LocallyFinite]
    (D k R t u v : ℕ) (hD : 2 ≤ D) (hk : 1 ≤ k)
    (hG : IsRegularTree G D) (huv : G.Adj u v) (ht : t ≤ R)
    (Z : RawRule k) (hZ : IsRule G k R Z) :
    (D : ℝ) / 2 * jointCondEntropy G R Z u v (sharedBits G k t u v) ≥
      (D - 1 : ℝ) * condEntropy G R Z v (viewBits G k t v) +
      condEntropy G R Z v (viewBits G k R v) := by sorry

end DistributedMIS.LocalLowerBound
