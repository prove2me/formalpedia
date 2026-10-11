-- Prove2me | Theorems.Thm_Algo2Lean_UnionFind_link_potential
-- name    : Algo2Lean.UnionFind.link_potential
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:55:25.101094+00:00
-- url     : https://prove2.me/theorems/a84849f0-1071-479e-a705-70a02a2a16f1
-- title:
--   Union-find: a rank link adds at most inverse-Ackermann potential
-- statement:
--   Let $S$ be valid and let distinct roots $l,w$ satisfy $\operatorname{rank}(l)\le\operatorname{rank}(w)$. Then
--   $$
--   \Phi(\operatorname{link}(S,l,w))\le\Phi(S)+\alpha(n).
--   $$
--   This is a bound on potential growth, not on elapsed program work. It is combined with compression bounds to pay for a complete union.
--
--   Here $n$ is the fixed number of elements, $\alpha(n)$ is `Algo2Lean.Ackermann.alpha`, and $\Phi$ is `Algo2Lean.UnionFind.potential`. Their definitions are in the separate Ackermann and union-find amortization definition bundles. The inverse is the least positive $k$ with $A_k(1)>n$, where $A_0(r)=r+1$ and $A_{k+1}(r)$ iterates $A_k$ exactly $r+1$ times starting at $r$.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/UnionFindAmortized.lean#L377-L411

import Definitions.Def_Algo2LeanLib_UnionFindAmortized
import Theorems.Thm_Algo2Lean_UnionFind_link_valid

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem Algo2Lean.UnionFind.link_potential :
    ∀ {n : Nat} {state : Algo2Lean.UnionFind.State n},
      Algo2Lean.UnionFind.Valid state →
        ∀ (loser winner : Fin n),
          Ne.{1} loser winner →
            Eq.{1} (state.parent loser) loser →
              Eq.{1} (state.parent winner) winner →
                LE.le.{0} (state.rank loser) (state.rank winner) →
                  LE.le.{0}
                    (Algo2Lean.UnionFind.potential (Algo2Lean.UnionFind.link state loser winner))
                    (HAdd.hAdd.{0, 0, 0} (Algo2Lean.UnionFind.potential state)
                      (Algo2Lean.Ackermann.alpha n)) := by
  sorry
