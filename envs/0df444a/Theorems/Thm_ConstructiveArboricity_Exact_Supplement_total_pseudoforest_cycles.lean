-- Prove2me | Theorems.Thm_ConstructiveArboricity_Exact_Supplement_total_pseudoforest_cycles
-- name    : ConstructiveArboricity.Exact.Supplement.total_pseudoforest_cycles
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:17:00.603869+00:00
-- url     : https://prove2.me/theorems/3620cdb4-9c46-4b2a-9daf-1d06a693acd7
-- title:
--   Lemma 3.2 — Total number of cycles
-- statement:
--   Let $G$ be a finite simple graph with $n$ vertices, $m$ edges and any supplied $k$-out orientation, where $k\ge1$. Lines 1–5 of Algorithm 1 construct a partition into $k$ pseudoforests with a total number $Z$ of cycles satisfying
--
--   $$ Z\le C_Z n\log(k+2). $$
--
--   A fixed RAM implementation outputs every edge color in time at most $C_T(1+m+nk\log(n+2))$. Both positive constants are uniform over all input parameters, and the execution follows the descending extraction-and-deletion rounds. The time includes preparing outgoing adjacency lists and all deletions. This gives the cycle-sensitive input to the conversion step.
--
--   Differences from the source:
--   - encoding: finite graphs and algorithms with uniform asymptotic bounds → edge-indexed finite labels and one finite word-RAM program, with uniform positive constants; reason: labels preserve every finite graph up to relabeling; Runs charges actual instructions including memory, subroutines and output
--   - encoding: asymptotic running times with log n → an additive unit and log(n+2) in the finite-size bounds; reason: totalizes empty and small inputs without changing the asymptotic parameter dependence
--   - encoding: O(n log k) total cycles → Z at most C_Z n log(k+2); reason: shifted logarithms include k=1 without a false zero-cycle bound
--   - encoding: unspecified vertex scan and outgoing-edge order in Algorithm 2 → vertices and available outgoing edges are scanned in increasing input identity order; reason: fixes the source algorithm’s permitted choices deterministically; adjacency lists can retain this order under constant-time linked-list deletions
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026). This is the pinned submission, not an assertion of conference acceptance. Lemma 3.2, PDF/printed p.12.

import Definitions.Def_ConstructiveArboricity_Exact_Supplement_Extraction

namespace ConstructiveArboricity.Exact.Supplement

/-- Lemma 3.2, p.12, including outgoing-list preparation and all deletions. -/
theorem total_pseudoforest_cycles :
    ∃ (P : Program) (b : ℕ) (Cz Ct : ℝ), 0 < b ∧ 0 < Cz ∧ 0 < Ct ∧
    ∀ (G : Graph) (k : ℕ) (tail : Fin G.m → Fin G.n),
      1 ≤ k → G.IsKOut k tail →
      ∀ W, WidthEnough b (G.n + G.m + k) W →
      ∃ (c : Fin G.m → Fin k) (t : ℕ),
        FirstStage G tail k c ∧ G.PseudoforestPartition k c ∧
        (totalCycles G c : ℝ) ≤ Cz * G.n * logSize k ∧
        Runs P (orientationInput G k tail) (G.partitionOutput k c) W t ∧
        (t : ℝ) ≤ Ct * (1 + G.m + G.n * k * logSize G.n) := by sorry

end ConstructiveArboricity.Exact.Supplement
