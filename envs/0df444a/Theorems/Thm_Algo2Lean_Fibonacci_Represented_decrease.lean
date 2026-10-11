-- Prove2me | Theorems.Thm_Algo2Lean_Fibonacci_Represented_decrease
-- name    : Algo2Lean.Fibonacci.Represented.decrease
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:53:45.337994+00:00
-- url     : https://prove2.me/theorems/7a615f0e-5bd9-4ac9-9fc9-2e6ead6d9e57
-- title:
--   Fibonacci heap: a strict decrease preserves the mathematical representation
-- statement:
--   For a represented Fibonacci forest and a present handle whose new key is strictly smaller, there exist a final snapshot, forest and cut count realizing `DecreaseRun`. The final forest remains represented, changes exactly that handle's key, and satisfies the pure `Decrease` accounting relation. This supplies the mathematical execution reused by the compiled method proof.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciKeyUpdate.lean#L444-L476

import Definitions.Def_Algo2LeanLib_FibonacciKeyUpdate
import Theorems.Thm_Algo2Lean_Fibonacci_RootBoundary_cut

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem Algo2Lean.Fibonacci.Represented.decrease :
    ∀ {state : Algo2Lean.Fibonacci.Snapshot} {forest : Algo2Lean.Fibonacci.Forest},
      Algo2Lean.Fibonacci.Represented state forest →
        ∀ (vertex key : Int),
          Ne.{1} (state.present vertex) (0 : Int) →
            LT.lt.{0} key (state.keys vertex) →
              Exists.{1} fun final =>
                Exists.{1} fun outputForest =>
                  Exists.{1} fun cuts =>
                    Algo2Lean.Fibonacci.DecreaseRun state final vertex key cuts ∧
                      Algo2Lean.Fibonacci.Represented final outputForest ∧
                        Algo2Lean.Fibonacci.EntryChange forest.entries outputForest.entries vertex
                            (state.keys vertex) key ∧
                          Algo2Lean.Fibonacci.Decrease forest.counts outputForest.counts cuts := by
  sorry
