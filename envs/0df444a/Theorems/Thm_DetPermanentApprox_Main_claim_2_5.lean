-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_claim_2_5
-- name    : DetPermanentApprox.Main.claim_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:55.695213+00:00
-- url     : https://prove2.me/theorems/852f0197-16e7-4f2c-9d3a-b15c71307bf1
-- title:
--   Claim 2.5 — Opposite-part vertex correlation
-- statement:
--   Let $A$ be any entrywise nonnegative real matrix, let $G$ be its bipartite positive-support graph with weights $w=A$ on its edges, and let $u$ be a row vertex and $v$ a column vertex. Then
--
--   $$Z_G(w)Z_{G-u-v}(w)\ge Z_{G-u}(w)Z_{G-v}(w).$$
--
--   Each partition function sums over all matchings of the indicated induced subgraph. The assertion applies to opposite bipartition classes, including when the two vertices have the same numerical index. It is the correlation inequality used at the minimizing weights.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
--   - generalization: weights w fixed at a field minimizer in the positive-permanent reduced-support setting → arbitrary nonnegative bipartite matrix weights; reason: the weight-preserving injection on p.9 uses none of the minimizer, total-support, or positive-permanent assumptions; substituting the minimizing weight matrix recovers the full source claim
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Claim 2.5, p. 9 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Matchings

namespace DetPermanentApprox.Main

theorem claim_2_5 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (u v : Fin n) :
    let G := supportGraph A
    let w := supportWeights A
    Z G w * restrictedZ G ((Finset.univ.erase (Sum.inl u)).erase (Sum.inr v)) w ≥
      restrictedZ G (Finset.univ.erase (Sum.inl u)) w *
        restrictedZ G (Finset.univ.erase (Sum.inr v)) w := by sorry

end DetPermanentApprox.Main
