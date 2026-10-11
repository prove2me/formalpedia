-- Prove2me | Theorems.Thm_Algo2Lean_Fibonacci_RootBoundary_cut
-- name    : Algo2Lean.Fibonacci.RootBoundary.cut
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:51:33.691249+00:00
-- url     : https://prove2.me/theorems/ace48f86-4115-4ba3-bf79-864afd14fa60
-- title:
--   Fibonacci heap: cutting a child preserves the root-boundary representation
-- statement:
--   Suppose a snapshot satisfies `RootBoundary` for a forest containing a parent in an ancestor context. If that parent's children split as `before ++ child :: after`, the pure snapshot cut operation yields a snapshot representing the corresponding forest with that child made an unmarked root and removed from its parent. Boundary observations remain represented; this local theorem needs no intermediate rank assumption.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciDecrease.lean#L135-L247

import Definitions.Def_Algo2LeanLib_FibonacciDecrease

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem Algo2Lean.Fibonacci.RootBoundary.cut :
    ∀ {state : Algo2Lean.Fibonacci.Snapshot} {context : List.{0} Algo2Lean.Fibonacci.Ancestor}
      {parent child : Algo2Lean.Fibonacci.Node} {rest : Algo2Lean.Fibonacci.Forest},
      Algo2Lean.Fibonacci.RootBoundary state
          (List.cons.{0} (Algo2Lean.Fibonacci.Ancestors.plug context parent) rest) →
        ∀ (before after : List.{0} Algo2Lean.Fibonacci.Node),
          Eq.{1} parent.children (HAppend.hAppend.{0, 0, 0} before (List.cons.{0} child after)) →
            Algo2Lean.Fibonacci.RootBoundary (state.cut child.vertex parent.vertex)
              (List.cons.{0}
                (Algo2Lean.Fibonacci.Ancestors.plug context
                  (parent.withChildren (HAppend.hAppend.{0, 0, 0} before after)))
                (List.cons.{0} (child.withMark Bool.false) rest)) := by
  sorry
