-- Prove2me | Theorems.Thm_Algo2Lean_Kruskal_Scan_minimum_spanning_forest
-- name    : Algo2Lean.Kruskal.Scan.minimum_spanning_forest
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:55:37.296967+00:00
-- url     : https://prove2.me/theorems/ab8ded95-b7ee-4e6c-b7a0-30fdae35871a
-- title:
--   Kruskal: a sorted scan produces a minimum spanning forest
-- statement:
--   If `Scan input [] result` follows the accept-if-disconnected rule from no selected edges and `input` is sorted by nondecreasing integer weight, then `MinimumSpanningForest input result` holds. The result is acyclic, uses input edges, spans the input connectivity, and weighs no more than every other spanning forest of the same input.
--
--   This theorem is independent of a data structure or program execution. Disconnected inputs, parallel edges, loops, ties, and negative weights are permitted; disconnected inputs produce a forest rather than a single spanning tree. It is the mathematical correctness result reused by the compiled algorithm.
--
--   Part of the [Algo2Lean](https://www.algo2lean.com/) CLRS series: *Introduction to Algorithms*, fourth edition, Chapter 21, §21.2 (Kruskal), the safe-edge principle in Theorem 21.1 (§21.1), and the union-by-rank/path-compression bound in Theorem 19.14 (§19.4).
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/KruskalMath.lean#L560-L571

import Definitions.Def_Algo2LeanLib_KruskalMath
import Theorems.Thm_Algo2Lean_Kruskal_Scan_weight_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem Algo2Lean.Kruskal.Scan.minimum_spanning_forest :
    ∀ {input result : List.{0} Algo2Lean.Kruskal.Edge},
      Algo2Lean.Kruskal.Scan input List.nil.{0} result →
        Algo2Lean.Kruskal.Sorted input → Algo2Lean.Kruskal.MinimumSpanningForest input result := by
  sorry
