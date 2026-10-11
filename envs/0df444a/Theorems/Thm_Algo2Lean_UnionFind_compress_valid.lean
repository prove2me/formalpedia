-- Prove2me | Theorems.Thm_Algo2Lean_UnionFind_compress_valid
-- name    : Algo2Lean.UnionFind.compress_valid
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:52:30.12084+00:00
-- url     : https://prove2.me/theorems/10e1e87a-4a99-4117-a306-e7aa9f819316
-- title:
--   Union-find: one path-compression write preserves validity
-- statement:
--   For a valid finite union-find state $S$ on `Fin n` and any vertex $v$, `compress S v` is valid. This operation redirects the single parent pointer at $v$ to its represented root; the full recursive path operation is `compressPath`.
--
--   Validity is the pure forest/rank/accounting invariant used by all subsequent runtime proofs. This theorem has no heap, generated-code, graph, or execution-history premise.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/UnionFind.lean#L189-L214

import Definitions.Def_Algo2LeanLib_UnionFind

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem Algo2Lean.UnionFind.compress_valid :
    ∀ {n : Nat} {state : Algo2Lean.UnionFind.State n},
      Algo2Lean.UnionFind.Valid state →
        ∀ (vertex : Fin n), Algo2Lean.UnionFind.Valid (Algo2Lean.UnionFind.compress state vertex) := by
  sorry
