-- Prove2me | Theorems.Thm_Algo2Lean_UnionFind_link_valid
-- name    : Algo2Lean.UnionFind.link_valid
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:52:33.072003+00:00
-- url     : https://prove2.me/theorems/39e4e8cf-8bc5-4ede-9074-7cdc12e6abbe
-- title:
--   Union-find: linking roots by rank preserves validity
-- statement:
--   Let $S$ be a valid forest and let $l\ne w$ be roots with $\operatorname{rank}(l)\le\operatorname{rank}(w)$. Then `link S l w` is valid: it makes $l$ a child of $w$, raises $w$'s rank only on a tie, updates component representatives, and transfers root mass.
--
--   The theorem is independent of a program representation. It is the structural justification for union by rank and preserves the invariant needed for both logarithmic path bounds and inverse-Ackermann amortization.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/UnionFind.lean#L258-L332

import Definitions.Def_Algo2LeanLib_UnionFind

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem Algo2Lean.UnionFind.link_valid :
    ∀ {n : Nat} {state : Algo2Lean.UnionFind.State n},
      Algo2Lean.UnionFind.Valid state →
        ∀ (loser winner : Fin n),
          Ne.{1} loser winner →
            Eq.{1} (state.parent loser) loser →
              Eq.{1} (state.parent winner) winner →
                LE.le.{0} (state.rank loser) (state.rank winner) →
                  Algo2Lean.UnionFind.Valid (Algo2Lean.UnionFind.link state loser winner) := by
  sorry
