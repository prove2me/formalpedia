-- Prove2me | Theorems.Thm_Algo2Lean_UnionFind_Operations_amortized
-- name    : Algo2Lean.UnionFind.Operations.amortized
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:56:43.812578+00:00
-- url     : https://prove2.me/theorems/3e112ac0-f8d7-49e4-b85a-08fb879f18c8
-- title:
--   Union-find: compositional inverse-Ackermann running time for mixed operations
-- statement:
--   Let `Operations before after f u C` be a finite sequence in the pure parent/rank model, with $f$ explicit find operations, $u$ union operations and charged cost $C$. If the initial state is valid, the final state is valid and
--   $$
--   C+2\Phi(after)\le2\Phi(before)+f(2\alpha(n)+3)+u(6\alpha(n)+7).
--   $$
--   A union's two internal finds are included in its union cost, not counted again in $f$. A path of length $p$ costs $2p+1$ for a find; a union with successive path lengths $p,q$ costs $2(p+q)+3$.
--
--   This theorem quantifies over `Operations`, not directly over arbitrary mutable program transcripts. The compiled constructor and method contracts connect those model transitions and costs to actual calls. Retaining the initial potential makes the theorem reusable on a suffix of an existing computation.
--
--   Here $n$ is the fixed number of elements, $\alpha(n)$ is `Algo2Lean.Ackermann.alpha`, and $\Phi$ is `Algo2Lean.UnionFind.potential`. Their definitions are in the separate Ackermann and union-find amortization definition bundles. The inverse is the least positive $k$ with $A_k(1)>n$, where $A_0(r)=r+1$ and $A_{k+1}(r)$ iterates $A_k$ exactly $r+1$ times starting at $r$.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/UnionFindAmortized.lean#L601-L620

import Definitions.Def_Algo2LeanLib_UnionFindAmortized
import Theorems.Thm_Algo2Lean_UnionFind_compress_valid
import Theorems.Thm_Algo2Lean_UnionFind_link_valid
import Theorems.Thm_Algo2Lean_UnionFind_link_potential
import Theorems.Thm_Algo2Lean_UnionFind_compressPath_amortized

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem Algo2Lean.UnionFind.Operations.amortized :
    ∀ {n : Nat} {before after : Algo2Lean.UnionFind.State n} {finds unions cost : Nat},
      Algo2Lean.UnionFind.Operations before after finds unions cost →
        Algo2Lean.UnionFind.Valid before →
          Algo2Lean.UnionFind.Valid after ∧
            LE.le.{0}
              (HAdd.hAdd.{0, 0, 0} cost
                (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential after)))
              (HAdd.hAdd.{0, 0, 0}
                (HAdd.hAdd.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential before))
                  (HMul.hMul.{0, 0, 0} finds
                    (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.Ackermann.alpha n))
                      (3 : Nat))))
                (HMul.hMul.{0, 0, 0} unions
                  (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (6 : Nat) (Algo2Lean.Ackermann.alpha n))
                    (7 : Nat)))) := by
  sorry
