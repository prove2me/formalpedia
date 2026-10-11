-- Prove2me | Theorems.Thm_Algo2Lean_Kruskal_Scan_weight_le
-- name    : Algo2Lean.Kruskal.Scan.weight_le
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:52:31.590088+00:00
-- url     : https://prove2.me/theorems/2133157d-46b4-4036-96a4-9ed4ff3e484f
-- title:
--   Kruskal: the sorted-edge exchange inequality
-- statement:
--   Suppose `Scan pending selected result`, the pending edges are in nondecreasing weight order, and the already selected edges form a forest. Let `other` be any competitor forest that contains every selected edge, uses only selected or pending edges, and connects the endpoints of every pending edge. Then
--   $$
--   \operatorname{weight}(result)\le\operatorname{weight}(other).
--   $$
--   Weights are arbitrary integers; equal weights are permitted. This pure graph theorem contains no union-find, heap, compiler or runtime hypothesis. It is the exchange argument underlying the minimum spanning forest result and the safe-edge principle of CLRS fourth-edition Theorem 21.1.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/KruskalMath.lean#L485-L558

import Definitions.Def_Algo2LeanLib_KruskalMath

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem Algo2Lean.Kruskal.Scan.weight_le :
    ∀ {pending selected result : List.{0} Algo2Lean.Kruskal.Edge},
      Algo2Lean.Kruskal.Scan pending selected result →
        Algo2Lean.Kruskal.Sorted pending →
          Algo2Lean.Kruskal.Forest selected →
            ∀ (other : List.{0} Algo2Lean.Kruskal.Edge),
              Algo2Lean.Kruskal.Forest other →
                (∀ (edge : Algo2Lean.Kruskal.Edge),
                    Membership.mem.{0, 0} selected edge → Membership.mem.{0, 0} other edge) →
                  (∀ (edge : Algo2Lean.Kruskal.Edge),
                      Membership.mem.{0, 0} other edge →
                        Membership.mem.{0, 0} pending edge ∨ Membership.mem.{0, 0} selected edge) →
                    (∀ (edge : Algo2Lean.Kruskal.Edge),
                        Membership.mem.{0, 0} pending edge →
                          Algo2Lean.Kruskal.Connected other edge.source edge.target) →
                      LE.le.{0} (Algo2Lean.Kruskal.weight result) (Algo2Lean.Kruskal.weight other) := by
  sorry
