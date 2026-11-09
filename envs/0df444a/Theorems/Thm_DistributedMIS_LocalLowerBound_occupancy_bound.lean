-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_occupancy_bound
-- name    : DistributedMIS.LocalLowerBound.occupancy_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:13.381567+00:00
-- url     : https://prove2.me/theorems/7d267266-c106-42ef-937a-8d172a5b7ec7
-- title:
--   Theorem 1.2 — Occupancy bound
-- statement:
--   There is an absolute D₀ such that, for all integers D≥D₀ and k with D≤log k≤D², every symmetric radius-r rule A on the infinite D-regular tree, for every finite r≥1, satisfies
--
--   $$\epsilon(A)=0\quad\Longrightarrow\quad p(A)\le\min\{1,5000r\log D/D\}.$$
--
--   The threshold is independent of r and the rule. This is the full technical occupancy theorem, with the constant 5000 retained from its statement and the proof on p. 29.
--
--   Differences from the source:
--   - encoding: the infinite D-regular tree with coordinates [k] and output 0 → a SimpleGraph on ℕ satisfying IsRegularTree, coordinates Fin k, and output Option (Fin k); reason: all countable regular trees are isomorphic; coordinate a is source a+1 and none is source 0; all graph automorphisms act, including rooted branch permutations
--   - encoding: finite conditional probabilities of independent fair edge matrices → exact uniform cylinder sums with transposed reverse orientations; reason: only the finitely many required edge variables are averaged; this is the marginal of the infinite fair product law, with arbitrary finite radius retained
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Theorem 1.2, printed/PDF pp. 4

import Definitions.Def_DistributedMIS_LocalLowerBound_Iteration

namespace DistributedMIS.LocalLowerBound

theorem occupancy_bound : ∃ D₀ : ℕ, 3 ≤ D₀ ∧ ∀ (D k : ℕ), D₀ ≤ D →
    (D : ℝ) ≤ Real.log k → Real.log k ≤ (D : ℝ)^2 →
    ∀ (G : SimpleGraph ℕ) [G.LocallyFinite], IsRegularTree G D →
    ∀ (r : ℕ) (A : RawRule k), 1 ≤ r → IsRule G k r A →
    ∀ u v, G.Adj u v → conflict G r A u v = 0 →
      occupancy G r A v ≤ min 1 (5000 * r * Real.log D / D) := by sorry

end DistributedMIS.LocalLowerBound
