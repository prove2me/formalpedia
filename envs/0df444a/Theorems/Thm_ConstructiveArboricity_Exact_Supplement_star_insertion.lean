-- Prove2me | Theorems.Thm_ConstructiveArboricity_Exact_Supplement_star_insertion
-- name    : ConstructiveArboricity.Exact.Supplement.star_insertion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:20:45.7874+00:00
-- url     : https://prove2.me/theorems/b10004cf-4893-48cb-ae77-a4d5738ff3a1
-- title:
--   Theorem 4 — Star Insertion
-- statement:
--   Let $H$ be a finite simple graph with $n$ vertices and $m$ edges, let $r$ be a specified vertex, and suppose the edges of $H-r$ are supplied as a partition into $k$ forests. One fixed RAM program returns a partition of all edges of $H$ into $k$ forests, allowing old edges to change color, or returns No precisely when no such partition exists. Its running time is
--
--   $$ (nk+m)^{1+o(1)}. $$
--
--   More precisely, the same program and width multiplier work for every $\varepsilon>0$; there is then a positive input-independent $C_\varepsilon$ bounding its time by $C_\varepsilon(2+nk+m)^{1+\varepsilon}$. The program must execute its subroutines within the charged RAM semantics. The domain includes edgeless graphs and $k=0$; no acyclic optimal-flow assumption or flow oracle is supplied. This companion theorem gives a constructive global extension-or-rejection procedure.
--
--   Differences from the source:
--   - encoding: finite graphs and algorithms with uniform asymptotic bounds → edge-indexed finite labels and one finite word-RAM program, with uniform positive constants; reason: labels preserve every finite graph up to relabeling; Runs charges actual instructions including memory, subroutines and output
--   - encoding: (nk+m)^(1+o(1)) time → one program before every epsilon>0, then a uniform C_epsilon times (2+nk+m)^(1+epsilon); reason: expresses the full subpolynomial exponent with a finite-size shift and preserves all input parameters
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026). This is the pinned submission, not an assertion of conference acceptance. Theorem 4, PDF/printed p.14.

import Definitions.Def_ConstructiveArboricity_Exact_Supplement_Interface

namespace ConstructiveArboricity.Exact.Supplement

/-- Theorem 4, p.14. One ordinary program precedes every exponent epsilon;
there is no free flow oracle, and empty/k=0 inputs remain in the domain. -/
theorem star_insertion :
    ∃ (P : Program) (b : ℕ), 0 < b ∧
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (G : Graph) (k : ℕ) (r : Fin G.n) (a : StarInput G k r),
      ∀ W, WidthEnough b (G.n + G.m + k) W →
      ∃ (out : List ℤ) (t : ℕ), decisionOutput G k out ∧
        Runs P (starInput G k r a) out W t ∧
        (t : ℝ) ≤ C * (2 + G.n * k + G.m : ℝ) ^ (1 + ε) := by sorry

end ConstructiveArboricity.Exact.Supplement
