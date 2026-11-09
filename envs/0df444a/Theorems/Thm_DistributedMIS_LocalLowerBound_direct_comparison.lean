-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_direct_comparison
-- name    : DistributedMIS.LocalLowerBound.direct_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:20.214627+00:00
-- url     : https://prove2.me/theorems/8940df05-60bc-4b6e-b1d9-18f94daeab7b
-- title:
--   Proposition 10.1 — Direct comparison with a smaller-view rule
-- statement:
--   Let Z be any symmetric radius-R rule, 0≤t≤R, and let Q be its actual conditional resampling onto N_t. At an adjacent pair u,v,
--
--   $$p(Q)=p(Z),\quad \sqrt{\epsilon(Q)}\le\sqrt{\epsilon(Z)}+
--   \sqrt{\frac2D\bigl(H(Z_v\mid N_t(v))-H(Z_v\mid N_R(v))\bigr)}.$$
--
--   Q is a symmetric radius-t rule. If ε(Z)=0, z=p(Z), and at most m≥1 nonzero coordinates are possible given each smaller view, then
--
--   $$\epsilon(Q)\le\frac{2z}{D}\log(em/z).$$
--
--   The right side is zero at z=0. The comparison has no factor R-t.
--
--   Differences from the source:
--   - encoding: the infinite D-regular tree with coordinates [k] and output 0 → a SimpleGraph on ℕ satisfying IsRegularTree, coordinates Fin k, and output Option (Fin k); reason: all countable regular trees are isomorphic; coordinate a is source a+1 and none is source 0; all graph automorphisms act, including rooted branch permutations
--   - encoding: finite conditional probabilities of independent fair edge matrices → exact uniform cylinder sums with transposed reverse orientations; reason: only the finitely many required edge variables are averaged; this is the marginal of the infinite fair product law, with arbitrary finite radius retained
--   - generalization: the large-degree application of the regular-tree model → all D≥2 and k≥1; reason: the structural entropy and symmetry statements need no logarithmic parameter regime; every source instance is included
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Proposition 10.1, printed/PDF pp. 26

import Definitions.Def_DistributedMIS_LocalLowerBound_Iteration

namespace DistributedMIS.LocalLowerBound

theorem direct_comparison (G : SimpleGraph ℕ) [G.LocallyFinite]
    (D k R t u v : ℕ) (hD : 2 ≤ D) (hk : 1 ≤ k) (hG : IsRegularTree G D)
    (huv : G.Adj u v) (ht : t ≤ R) (Z : RawRule k) (hZ : IsRule G k R Z) :
    let Q := resample G R t Z
    IsRule G k t Q ∧ occupancy G t Q v = occupancy G R Z v ∧
    Real.sqrt (conflict G t Q u v) ≤ Real.sqrt (conflict G R Z u v) +
      Real.sqrt ((2 / (D : ℝ)) *
        (condEntropy G R Z v (viewBits G k t v) -
         condEntropy G R Z v (viewBits G k R v))) ∧
    ∀ m : ℕ, 1 ≤ m → conflict G R Z u v = 0 → ShortSupport G R t m Z →
      conflict G t Q u v ≤ 2 / (D : ℝ) * massEntropy m (occupancy G R Z v) := by sorry

end DistributedMIS.LocalLowerBound
