-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_occupancy_total_conflict
-- name    : DistributedMIS.LocalLowerBound.occupancy_total_conflict
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:24.65069+00:00
-- url     : https://prove2.me/theorems/d8dc472d-6abc-4e02-b6ea-482356a0f77e
-- title:
--   Lemma 9.2 — Occupancy from a total conflict budget
-- statement:
--   Start the actual radius-reduction sequence from a symmetric radius-r rule, r≥1, with the paper's list sizes and numerical regime. Let p=p(A_0), w_j=ε(D_j), S=ε(A_r)+Σ_{j<r}w_j, and b=2100 log D/D. Then
--
--   $$p\le rb+\sqrt{36r+2}\sqrt S.$$
--
--   The rules and their truncation lists are the recursively computed ones, not arbitrary objects assumed to satisfy these estimates. The bound aggregates all occupancy losses.
--
--   Differences from the source:
--   - encoding: the infinite D-regular tree with coordinates [k] and output 0 → a SimpleGraph on ℕ satisfying IsRegularTree, coordinates Fin k, and output Option (Fin k); reason: all countable regular trees are isomorphic; coordinate a is source a+1 and none is source 0; all graph automorphisms act, including rooted branch permutations
--   - encoding: finite conditional probabilities of independent fair edge matrices → exact uniform cylinder sums with transposed reverse orientations; reason: only the finitely many required edge variables are averaged; this is the marginal of the infinite fair product law, with arbitrary finite radius retained
--   - encoding: one unspecified sufficiently large absolute D₀ → an existential absolute threshold before D, k, radius and rule; reason: the finitely many thresholds can be unified by their maximum; none depends on the radius or rule
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Lemma 9.2, printed/PDF pp. 24

import Definitions.Def_DistributedMIS_LocalLowerBound_Iteration

namespace DistributedMIS.LocalLowerBound

theorem occupancy_total_conflict : ∃ D₀ : ℕ, 3 ≤ D₀ ∧ ∀ (D k : ℕ), D₀ ≤ D →
    (D : ℝ) ≤ Real.log k → Real.log k ≤ (D : ℝ)^2 →
    ∀ (G : SimpleGraph ℕ) [G.LocallyFinite], IsRegularTree G D →
    ∀ (r : ℕ) (A : RawRule k), 1 ≤ r → IsRule G k r A →
    ∀ u v, G.Adj u v →
      occupancy G r A v ≤ (r : ℝ) * lossBase D +
        Real.sqrt (36 * (r : ℝ) + 2) *
          Real.sqrt (totalConflict G r (retainedSize D k) A u v) := by sorry

end DistributedMIS.LocalLowerBound
