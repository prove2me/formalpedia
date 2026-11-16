-- Prove2me | Theorems.Thm_ConstructiveArboricity_Exact_Supplement_additive_one
-- name    : ConstructiveArboricity.Exact.Supplement.additive_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:19:02.670207+00:00
-- url     : https://prove2.me/theorems/0379f987-1cbc-4e4e-9500-80ed2a9bcf6d
-- title:
--   Theorem 3 — Constructive additive-one decomposition
-- statement:
--   Let $G$ be a finite simple graph with $n$ vertices and $m$ edges, and let any $k$-out orientation be supplied. There is one RAM algorithm returning a color for every edge, with each of its $k+1$ available color classes a forest, in time at most
--
--   $$ C\bigl(1+m\log(n+2)+nk\log^2(n+2)\bigr). $$
--
--   The constant is uniform over the graph, its orientation and $k$. No optimality of the supplied orientation, density condition or upper bound on $k$ is required. Empty forests and isolated vertices are retained implicitly; $k=0$ is included. This companion theorem provides the constructive additive-one partition.
--
--   Differences from the source:
--   - encoding: finite graphs and algorithms with uniform asymptotic bounds → edge-indexed finite labels and one finite word-RAM program, with uniform positive constants; reason: labels preserve every finite graph up to relabeling; Runs charges actual instructions including memory, subroutines and output
--   - encoding: asymptotic running times with log n → an additive unit and log(n+2) in the finite-size bounds; reason: totalizes empty and small inputs without changing the asymptotic parameter dependence
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026). This is the pinned submission, not an assertion of conference acceptance. Theorem 3, PDF/printed p.9.

import Definitions.Def_ConstructiveArboricity_Exact_Supplement_Interface

namespace ConstructiveArboricity.Exact.Supplement

/-- Theorem 3, p.9. Includes all supplied k-out bounds, including k=0. -/
theorem additive_one :
    ∃ (P : Program) (b : ℕ) (C : ℝ), 0 < b ∧ 0 < C ∧
    ∀ (G : Graph) (k : ℕ) (tail : Fin G.m → Fin G.n),
      G.IsKOut k tail →
      ∀ W, WidthEnough b (G.n + G.m + k) W →
      ∃ (c : Fin G.m → Fin (k+1)) (t : ℕ),
        G.ForestPartition (k+1) c ∧
        Runs P (orientationInput G k tail) (G.partitionOutput (k+1) c) W t ∧
        (t : ℝ) ≤ C * (1 + G.m * logSize G.n + G.n * k * (logSize G.n)^2) := by sorry

end ConstructiveArboricity.Exact.Supplement
