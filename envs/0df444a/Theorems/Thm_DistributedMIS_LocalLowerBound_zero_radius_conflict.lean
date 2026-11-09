-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_zero_radius_conflict
-- name    : DistributedMIS.LocalLowerBound.zero_radius_conflict
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:15.451202+00:00
-- url     : https://prove2.me/theorems/af3464be-173d-4dce-b37d-d8c93178eb70
-- title:
--   Lemma 9.1 — Zero-radius conflict
-- statement:
--   For every symmetric radius-zero rule, let p denote occupancy and ε conflict across an adjacent pair of cliques. Then
--
--   $$\epsilon=p^2/2.$$
--
--   The view is empty, so the same probability vector is used everywhere. This identifies the exact terminal conflict of the reduction sequence, including p=0.
--
--   Differences from the source:
--   - encoding: the infinite D-regular tree with coordinates [k] and output 0 → a SimpleGraph on ℕ satisfying IsRegularTree, coordinates Fin k, and output Option (Fin k); reason: all countable regular trees are isomorphic; coordinate a is source a+1 and none is source 0; all graph automorphisms act, including rooted branch permutations
--   - encoding: finite conditional probabilities of independent fair edge matrices → exact uniform cylinder sums with transposed reverse orientations; reason: only the finitely many required edge variables are averaged; this is the marginal of the infinite fair product law, with arbitrary finite radius retained
--   - generalization: the large-degree application of the regular-tree model → all D≥2 and k≥1; reason: the structural entropy and symmetry statements need no logarithmic parameter regime; every source instance is included
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Lemma 9.1, printed/PDF pp. 24

import Definitions.Def_DistributedMIS_LocalLowerBound_Iteration

namespace DistributedMIS.LocalLowerBound

theorem zero_radius_conflict (G : SimpleGraph ℕ) [G.LocallyFinite]
    (D k u v : ℕ) (hD : 2 ≤ D) (hk : 1 ≤ k) (hG : IsRegularTree G D)
    (huv : G.Adj u v) (A : RawRule k) (hA : IsRule G k 0 A) :
    conflict G 0 A u v = (occupancy G 0 A v)^2 / 2 := by sorry

end DistributedMIS.LocalLowerBound
