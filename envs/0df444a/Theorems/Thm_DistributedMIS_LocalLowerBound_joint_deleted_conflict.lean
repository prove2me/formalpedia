-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_joint_deleted_conflict
-- name    : DistributedMIS.LocalLowerBound.joint_deleted_conflict
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:21.056835+00:00
-- url     : https://prove2.me/theorems/cbda1fa5-455a-4be5-b1c8-f70e11f210e8
-- title:
--   Proposition 10.3 — Joint deleted-conflict budget
-- statement:
--   For the actual reduction sequence from a zero-conflict radius-r rule, let p_j=p(A_j), w_j=ε(D_j), and ε_r=ε(A_r), with r≥1. Then
--
--   $$\epsilon_r+\sum_{j<r}w_j\le\frac{2p_1}{D}\log(emr/p_1)
--   \le\frac{2p_0}{D}\log(emr/p_0).$$
--
--   Both zero-mass expressions are defined by their continuous value zero. The result controls the joint conflict budget of all deleted parts and the final survivor.
--
--   Differences from the source:
--   - encoding: the infinite D-regular tree with coordinates [k] and output 0 → a SimpleGraph on ℕ satisfying IsRegularTree, coordinates Fin k, and output Option (Fin k); reason: all countable regular trees are isomorphic; coordinate a is source a+1 and none is source 0; all graph automorphisms act, including rooted branch permutations
--   - encoding: finite conditional probabilities of independent fair edge matrices → exact uniform cylinder sums with transposed reverse orientations; reason: only the finitely many required edge variables are averaged; this is the marginal of the infinite fair product law, with arbitrary finite radius retained
--   - generalization: the large-degree application of the regular-tree model → all D≥2 and k≥1; reason: the structural entropy and symmetry statements need no logarithmic parameter regime; every source instance is included
--   - generalization: the application list size m=DM → any integer m≥1; reason: the direct comparison and partition accounting use only the list size, so the source instance is included
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Proposition 10.3, printed/PDF pp. 28

import Definitions.Def_DistributedMIS_LocalLowerBound_Iteration

namespace DistributedMIS.LocalLowerBound

theorem joint_deleted_conflict (G : SimpleGraph ℕ) [G.LocallyFinite]
    (D k r m u v : ℕ) (hD : 2 ≤ D) (hk : 1 ≤ k) (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hG : IsRegularTree G D) (huv : G.Adj u v) (A : RawRule k)
    (hA : IsRule G k r A) (hzero : conflict G r A u v = 0) :
    totalConflict G r m A u v ≤
      2 / (D : ℝ) * massEntropy (m*r) (occupancy G (r-1) (iterateRule G r m A 1) v) ∧
    2 / (D : ℝ) * massEntropy (m*r) (occupancy G (r-1) (iterateRule G r m A 1) v) ≤
      2 / (D : ℝ) * massEntropy (m*r) (occupancy G r A v) := by sorry

end DistributedMIS.LocalLowerBound
