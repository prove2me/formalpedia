-- Prove2me | Theorems.Thm_ConstructiveArboricity_Exact_Supplement_rooted_construction
-- name    : ConstructiveArboricity.Exact.Supplement.rooted_construction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:22:04.835663+00:00
-- url     : https://prove2.me/theorems/d7da3c2b-87c5-4d5f-a984-5d2148869458
-- title:
--   Theorem 5 — Constructive partition by the rooted reduction
-- statement:
--   Let $G$ be a finite simple graph with $n$ vertices and any supplied $k$-out orientation. One RAM algorithm either constructs a partition of every edge into $k$ forests or correctly reports that no such partition exists. A positive uniform constant bounds its time by
--
--   $$ C\bigl(1+nk^2\log(n+2)\bigr). $$
--
--   The algorithm, width multiplier and constant precede all graphs, supplied orientations and values of $k$. The rejection branch excludes every possible partition, and the success branch assigns a color to every edge. The domain includes $k=0$ and empty graphs. This companion theorem states the complete constructive rooted-decision bound, including the execution and output work.
--
--   Differences from the source:
--   - encoding: finite graphs and algorithms with uniform asymptotic bounds → edge-indexed finite labels and one finite word-RAM program, with uniform positive constants; reason: labels preserve every finite graph up to relabeling; Runs charges actual instructions including memory, subroutines and output
--   - encoding: asymptotic running times with log n → an additive unit and log(n+2) in the finite-size bounds; reason: totalizes empty and small inputs without changing the asymptotic parameter dependence
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026). This is the pinned submission, not an assertion of conference acceptance. Theorem 5, PDF/printed p.29.

import Definitions.Def_ConstructiveArboricity_Exact_Supplement_Interface

namespace ConstructiveArboricity.Exact.Supplement

/-- Theorem 5, p.29. The supplied orientation is not required to be optimal. -/
theorem rooted_construction :
    ∃ (P : Program) (b : ℕ) (C : ℝ), 0 < b ∧ 0 < C ∧
    ∀ (G : Graph) (k : ℕ) (tail : Fin G.m → Fin G.n),
      G.IsKOut k tail →
      ∀ W, WidthEnough b (G.n + G.m + k) W →
      ∃ (out : List ℤ) (t : ℕ), decisionOutput G k out ∧
        Runs P (orientationInput G k tail) out W t ∧
        (t : ℝ) ≤ C * (1 + G.n * (k : ℝ)^2 * logSize G.n) := by sorry

end ConstructiveArboricity.Exact.Supplement
