-- Prove2me | Theorems.Thm_Algo2Lean_Fibonacci_SplitRepresented_consume_roots
-- name    : Algo2Lean.Fibonacci.SplitRepresented.consume_roots
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:53:40.573233+00:00
-- url     : https://prove2.me/theorems/b7de0c48-4a0f-46df-bab4-1f35c780e2ef
-- title:
--   Fibonacci heap: consolidation terminates with distinct root degrees
-- statement:
--   For a finite pending forest, represented buckets, a valid scratch bound and a supplied initial maximum at most 2 floor(log₂ n)+1, the pure snapshot model admits a finite `RootConsumption` run ending with no pending roots and a represented bucket forest. Entries and marks are preserved. If l links occur, final root count plus l equals the original pending-plus-bucket root count. The maximum scratch degree remains at most 2 floor(log₂ n)+1 for the represented heap size n.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciConsolidation.lean#L511-L595

import Definitions.Def_Algo2LeanLib_FibonacciConsolidation
import Theorems.Thm_Algo2Lean_Fibonacci_degree_logarithmic

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem Algo2Lean.Fibonacci.SplitRepresented.consume_roots :
    ∀ {state : Algo2Lean.Fibonacci.Snapshot} {pending buckets : Algo2Lean.Fibonacci.Forest},
      Algo2Lean.Fibonacci.SplitRepresented state pending buckets →
        Algo2Lean.Fibonacci.Buckets state buckets →
          ∀ (maximum : Int),
            Algo2Lean.Fibonacci.ScratchBound state maximum →
              ∀ (size : Nat),
                Eq.{1} state.size (↑size : Int) →
                  LE.le.{0} maximum
                      (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Int) (↑size.log2 : Int))
                        (1 : Int)) →
                    Exists.{1} fun after =>
                      Exists.{1} fun finalBuckets =>
                        Exists.{1} fun finalMaximum =>
                          Exists.{1} fun links =>
                            Algo2Lean.Fibonacci.RootConsumption state maximum after finalMaximum
                                (List.length.{0} pending) links ∧
                              Algo2Lean.Fibonacci.SplitRepresented after List.nil.{0} finalBuckets ∧
                                Algo2Lean.Fibonacci.Buckets after finalBuckets ∧
                                  Algo2Lean.Fibonacci.ScratchBound after finalMaximum ∧
                                    LE.le.{0} finalMaximum
                                        (HAdd.hAdd.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0} (2 : Int) (↑size.log2 : Int))
                                          (1 : Int)) ∧
                                      Eq.{1} (HAdd.hAdd.{0, 0, 0} links (List.length.{0} finalBuckets))
                                          (HAdd.hAdd.{0, 0, 0} (List.length.{0} pending)
                                            (List.length.{0} buckets)) ∧
                                        Eq.{1} after.size (↑size : Int) ∧
                                          List.Perm.{0} finalBuckets.entries
                                              (HAppend.hAppend.{0, 0, 0} pending buckets).entries ∧
                                            Eq.{1} finalBuckets.marks
                                              (HAppend.hAppend.{0, 0, 0} pending buckets).marks := by
  sorry
