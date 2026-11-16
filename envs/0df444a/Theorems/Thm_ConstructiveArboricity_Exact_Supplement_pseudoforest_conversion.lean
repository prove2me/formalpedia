-- Prove2me | Theorems.Thm_ConstructiveArboricity_Exact_Supplement_pseudoforest_conversion
-- name    : ConstructiveArboricity.Exact.Supplement.pseudoforest_conversion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:18:06.934479+00:00
-- url     : https://prove2.me/theorems/5db1bcc2-a838-4dd3-9797-e70dece14f1e
-- title:
--   Proposition 3.3 — Cycle-sensitive pseudoforest conversion
-- statement:
--   Let $G$ be a finite simple graph with $n$ vertices and $m$ edges. Suppose a supplied coloring partitions all edges into $k$ pseudoforests, with $Z$ cycles in total. A RAM implementation of the Blumenstock–Fischer surplus-edge conversion returns a partition into $k+1$ forests in time at most
--
--   $$ C\bigl(1+m\log(n+2)+nk+Zk\log(n+2)\bigr). $$
--
--   The implementation realizes the path swaps and cycle exchanges on the actual edge identities; all data-structure operations, scheduling, memory and output instructions are charged. The constant is independent of $G,k$ and the supplied partition. This is the paper's cycle-sensitive conversion bound, including its applicability to an arbitrary supplied pseudoforest partition.
--
--   Differences from the source:
--   - encoding: finite graphs and algorithms with uniform asymptotic bounds → edge-indexed finite labels and one finite word-RAM program, with uniform positive constants; reason: labels preserve every finite graph up to relabeling; Runs charges actual instructions including memory, subroutines and output
--   - encoding: asymptotic running times with log n → an additive unit and log(n+2) in the finite-size bounds; reason: totalizes empty and small inputs without changing the asymptotic parameter dependence
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026). This is the pinned submission, not an assertion of conference acceptance. Proposition 3.3, PDF/printed p.12.

import Definitions.Def_ConstructiveArboricity_Exact_Supplement_Conversion

namespace ConstructiveArboricity.Exact.Supplement

/-- Proposition 3.3, p.12, with the Z-sensitive analysis of Appendix A.
The RAM implementation must carry out the actual surplus-edge conversion;
all union-find, link-cut-tree, scheduling and output work is charged by Runs. -/
theorem pseudoforest_conversion :
    ∃ (P : Program) (b : ℕ) (C : ℝ), 0 < b ∧ 0 < C ∧
    ∀ (G : Graph) (k : ℕ) (c : Fin G.m → Fin k),
      G.PseudoforestPartition k c →
      ∀ W, WidthEnough b (G.n + G.m + k) W →
      ∃ (out : Fin G.m → Fin (k+1)) (t : ℕ),
        BFResult G c out ∧ G.ForestPartition (k+1) out ∧
        Runs P (coloringInput G k c) (G.partitionOutput (k+1) out) W t ∧
        (t : ℝ) ≤ C * (1 + G.m * logSize G.n + G.n * k +
          totalCycles G c * k * logSize G.n) := by sorry

end ConstructiveArboricity.Exact.Supplement
