-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_original_survivors
-- name    : DistributedMIS.LocalLowerBound.original_survivors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:27.751409+00:00
-- url     : https://prove2.me/theorems/60e0e294-73de-4ee1-9377-e65a06d878f6
-- title:
--   Lemma 10.2 — Original survivors have the required conditional probabilities
-- statement:
--   Use the computed lists P_j and views V_j=N_{r-j} of the reduction sequence. On the original rule's probability space, let Â_j retain the original coordinate if it passes every earlier list, and let D̂_j retain it precisely when it first fails list j. For every output a, including zero,
--
--   $$\Pr[(A_j)_v=a\mid V_j]=\Pr[(\widehat A_j)_v=a\mid V_j],\qquad
--   \Pr[(D_j)_v=a\mid V_j]=\Pr[(\widehat D_j)_v=a\mid V_j].$$
--
--   Every hatted rule is a symmetric radius-r restriction of A_0; if A_0 has zero conflict they all do. First-failure parts and the final survivor partition the original nonzero outputs. For j≥1 their nonzero conditional support at V_j has at most m coordinates. These are conditional-law equalities, with no redraw of the original coordinate.
--
--   Differences from the source:
--   - encoding: the infinite D-regular tree with coordinates [k] and output 0 → a SimpleGraph on ℕ satisfying IsRegularTree, coordinates Fin k, and output Option (Fin k); reason: all countable regular trees are isomorphic; coordinate a is source a+1 and none is source 0; all graph automorphisms act, including rooted branch permutations
--   - encoding: finite conditional probabilities of independent fair edge matrices → exact uniform cylinder sums with transposed reverse orientations; reason: only the finitely many required edge variables are averaged; this is the marginal of the infinite fair product law, with arbitrary finite radius retained
--   - generalization: the large-degree application of the regular-tree model → all D≥2 and k≥1; reason: the structural entropy and symmetry statements need no logarithmic parameter regime; every source instance is included
--   - generalization: the specific list size m=DM → any integer m≥1; reason: the tower-property and first-failure identities hold for every list size and include the paper choice
--   - generalization: the positive-radius reduction sequence of Sections 9 and 10 → also allow initial radius r=0; reason: at radius zero the survivor is the original rule, the deleted family is empty, and the support assertions have no applicable stages
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Lemma 10.2, printed/PDF pp. 27–28

import Definitions.Def_DistributedMIS_LocalLowerBound_Iteration

namespace DistributedMIS.LocalLowerBound

theorem original_survivors (G : SimpleGraph ℕ) [G.LocallyFinite]
    (D k r m : ℕ) (hD : 2 ≤ D) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hG : IsRegularTree G D) (A : RawRule k) (hA : IsRule G k r A) :
    (∀ j ≤ r,
      IsRule G k r (originalSurvivor G r m A j) ∧
      IsRestriction A (originalSurvivor G r m A j) ∧
      ∀ v ω a, condLaw G (r-j) (iterateRule G r m A j) v
        (viewBits G k (r-j) v) ω a =
      condLaw G r (originalSurvivor G r m A j) v (viewBits G k (r-j) v) ω a) ∧
    (∀ j < r,
      IsRule G k r (originalDeleted G r m A j) ∧
      IsRestriction A (originalDeleted G r m A j) ∧
      ∀ v ω a, condLaw G (r-j) (iterationDeleted G r m A j) v
        (viewBits G k (r-j) v) ω a =
      condLaw G r (originalDeleted G r m A j) v (viewBits G k (r-j) v) ω a) ∧
    (∀ u v, G.Adj u v → conflict G r A u v = 0 →
      (∀ j ≤ r, conflict G r (originalSurvivor G r m A j) u v = 0) ∧
      (∀ j < r, conflict G r (originalDeleted G r m A j) u v = 0)) ∧
    PartitionsOriginal G r m A ∧
    (∀ j, 1 ≤ j → j ≤ r → ShortSupport G r (r-j) m (originalSurvivor G r m A j)) ∧
    (∀ j, 1 ≤ j → j < r → ShortSupport G r (r-j) m (originalDeleted G r m A j)) := by sorry

end DistributedMIS.LocalLowerBound
