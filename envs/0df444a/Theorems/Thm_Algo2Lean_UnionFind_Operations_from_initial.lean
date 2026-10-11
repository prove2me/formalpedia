-- Prove2me | Theorems.Thm_Algo2Lean_UnionFind_Operations_from_initial
-- name    : Algo2Lean.UnionFind.Operations.from_initial
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:57:22.27224+00:00
-- url     : https://prove2.me/theorems/75a1a19e-e479-400d-89ee-59dca87476b6
-- title:
--   Union-find: inverse-Ackermann running time from singleton components
-- statement:
--   Starting from `initial n`, every pure mixed-operation sequence `Operations (initial n) after f u C` obeys
--   $$
--   C\le f(2\alpha(n)+3)+u(6\alpha(n)+7).
--   $$
--   The count $f$ records explicit finds; the two internal finds of each of the $u$ unions are already included in its charge. This finite inequality covers arbitrary interleavings of these operations. It excludes the separate constructor cost $n+1$.
--
--   This is a theorem about the pure `Operations` relation. To use it with mutable code, use the independently checked method contracts relating each actual call to its model transition and exact increments. Kruskal instead telescopes the same local contracts directly through its scan.
--
--   Here $n$ is the fixed number of elements, $\alpha(n)$ is `Algo2Lean.Ackermann.alpha`, and $\Phi$ is `Algo2Lean.UnionFind.potential`. Their definitions are in the separate Ackermann and union-find amortization definition bundles. The inverse is the least positive $k$ with $A_k(1)>n$, where $A_0(r)=r+1$ and $A_{k+1}(r)$ iterates $A_k$ exactly $r+1$ times starting at $r$.
--
--   This result belongs to the [Algo2Lean](https://www.algo2lean.com/) CLRS series, corresponding to *Introduction to Algorithms*, fourth edition, Chapter 19, §§19.3–19.4, especially the inverse-Ackermann analysis of Theorem 19.14. The API initializes a fixed universe in one constructor rather than interleaving individual MAKE-SET operations.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/UnionFindAmortized.lean#L623-L630

import Definitions.Def_Algo2LeanLib_UnionFindAmortized
import Theorems.Thm_Algo2Lean_UnionFind_Operations_amortized

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem Algo2Lean.UnionFind.Operations.from_initial :
    ∀ {n : Nat} {after : Algo2Lean.UnionFind.State n} {finds unions cost : Nat},
      Algo2Lean.UnionFind.Operations (Algo2Lean.UnionFind.initial n) after finds unions cost →
        LE.le.{0} cost
          (HAdd.hAdd.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} finds
              (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.Ackermann.alpha n))
                (3 : Nat)))
            (HMul.hMul.{0, 0, 0} unions
              (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (6 : Nat) (Algo2Lean.Ackermann.alpha n))
                (7 : Nat)))) := by
  sorry
