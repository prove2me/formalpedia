-- Prove2me | Theorems.Thm_Algo2Lean_UnionFind_compressPath_amortized
-- name    : Algo2Lean.UnionFind.compressPath_amortized
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:52:31.997842+00:00
-- url     : https://prove2.me/theorems/65fce70d-00ff-4a7b-9c76-2ef077c76f7b
-- title:
--   Union-find: inverse-Ackermann bound for full path compression
-- statement:
--   Suppose a valid state $S$ has a `Find S v r p` path from vertex $v$ to root $r$ with $p$ nonroot parent edges. Full compression of that path satisfies
--   $$
--   p+\Phi(\operatorname{compressPath}(S,v,p))\le\Phi(S)+\alpha(n)+1.
--   $$
--   This pure theorem charges traversed edges against lost potential. Compiled finds charge both traversal and pointer-rewrite events, which explains the factor two in their separate call contract.
--
--   Here $n$ is the fixed number of elements, $\alpha(n)$ is `Algo2Lean.Ackermann.alpha`, and $\Phi$ is `Algo2Lean.UnionFind.potential`. Their definitions are in the separate Ackermann and union-find amortization definition bundles. The inverse is the least positive $k$ with $A_k(1)>n$, where $A_0(r)=r+1$ and $A_{k+1}(r)$ iterates $A_k$ exactly $r+1$ times starting at $r$.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/UnionFindAmortized.lean#L553-L559

import Definitions.Def_Algo2LeanLib_UnionFindAmortized

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem Algo2Lean.UnionFind.compressPath_amortized :
    ∀ {n : Nat} {state : Algo2Lean.UnionFind.State n},
      Algo2Lean.UnionFind.Valid state →
        ∀ {vertex root : Fin n} {steps : Nat},
          Algo2Lean.UnionFind.Find state vertex root steps →
            LE.le.{0}
              (HAdd.hAdd.{0, 0, 0} steps
                (Algo2Lean.UnionFind.potential (Algo2Lean.UnionFind.compressPath state vertex steps)))
              (HAdd.hAdd.{0, 0, 0}
                (HAdd.hAdd.{0, 0, 0} (Algo2Lean.UnionFind.potential state)
                  (Algo2Lean.Ackermann.alpha n))
                (1 : Nat)) := by
  sorry
