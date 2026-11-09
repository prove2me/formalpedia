-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_conditional_truncation
-- name    : DistributedMIS.LocalLowerBound.conditional_truncation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:29.255216+00:00
-- url     : https://prove2.me/theorems/ea75eb95-5353-4888-a348-5275ea5b0e7c
-- title:
--   Proposition 8.6 — Conditional truncation
-- statement:
--   Use the paper's exact lists ℓ=⌈100 log(k+1)⌉, M=1000ℓ, m=DM, in the regime D≤log k≤D² above an absolute threshold. For a symmetric radius-s rule A with s≥1, let P_Y be the m most probable nonzero coordinates given Y=N_{s-1}(v), with coordinate-order ties. Let C keep the original output in P_Y and let B keep the other nonzero outputs. Put τ=p(B) and w=ε(B). Then
--
--   $$p(C)=p(A)-\tau,\qquad \epsilon(C)+w\le\epsilon(A),\qquad
--   \tau\le\frac{2100\log D}{D}+6\sqrt w.$$
--
--   Both rules retain symmetry and radius; the kept rule is conditionally supported on P_Y∪{0}. These conclusions quantify the actual truncation loss.
--
--   Differences from the source:
--   - encoding: the infinite D-regular tree with coordinates [k] and output 0 → a SimpleGraph on ℕ satisfying IsRegularTree, coordinates Fin k, and output Option (Fin k); reason: all countable regular trees are isomorphic; coordinate a is source a+1 and none is source 0; all graph automorphisms act, including rooted branch permutations
--   - encoding: finite conditional probabilities of independent fair edge matrices → exact uniform cylinder sums with transposed reverse orientations; reason: only the finitely many required edge variables are averaged; this is the marginal of the infinite fair product law, with arbitrary finite radius retained
--   - encoding: one unspecified sufficiently large absolute D₀ → an existential absolute threshold before D, k, radius and rule; reason: the finitely many thresholds can be unified by their maximum; none depends on the radius or rule
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Proposition 8.6, printed/PDF pp. 23

import Definitions.Def_DistributedMIS_LocalLowerBound_Iteration

namespace DistributedMIS.LocalLowerBound

theorem conditional_truncation : ∃ D₀ : ℕ, 3 ≤ D₀ ∧ ∀ (D k : ℕ), D₀ ≤ D →
    (D : ℝ) ≤ Real.log k → Real.log k ≤ (D : ℝ)^2 →
    ∀ (G : SimpleGraph ℕ) [G.LocallyFinite], IsRegularTree G D →
    ∀ (s : ℕ) (A : RawRule k), 1 ≤ s → IsRule G k s A →
    let P := truncationList G s (retainedSize D k) A
    let C := keepBy A P
    let B := deleteBy A P
    IsRule G k s C ∧ IsRule G k s B ∧
    SupportedOn G s C (viewBits G k (s-1)) P ∧
    ∀ u v, G.Adj u v →
      occupancy G s C v = occupancy G s A v - occupancy G s B v ∧
      conflict G s C u v + conflict G s B u v ≤ conflict G s A u v ∧
      occupancy G s B v ≤ lossBase D + 6 * Real.sqrt (conflict G s B u v) := by sorry

end DistributedMIS.LocalLowerBound
