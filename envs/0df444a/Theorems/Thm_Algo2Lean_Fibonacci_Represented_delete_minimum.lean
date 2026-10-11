-- Prove2me | Theorems.Thm_Algo2Lean_Fibonacci_Represented_delete_minimum
-- name    : Algo2Lean.Fibonacci.Represented.delete_minimum
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:53:43.448973+00:00
-- url     : https://prove2.me/theorems/f1b81c85-95ff-4d8d-b63b-03499f380783
-- title:
--   Fibonacci heap: deleting the minimum preserves a pending forest
-- statement:
--   Any represented nonempty Fibonacci forest admits a mathematical minimum deletion for its physical root rotation. The pending forest contains exactly the original entries with the selected minimum removed and has no more marks. Its root count plus one equals the previous root count plus the number p of promoted children, and p ≤ 2 floor(log₂ |entries|)+1. The resulting empty scratch table is suitable for consolidation.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciDeleteMin.lean#L250-L282

import Definitions.Def_Algo2LeanLib_FibonacciDeleteMin
import Theorems.Thm_Algo2Lean_Fibonacci_degree_logarithmic
import Theorems.Thm_Algo2Lean_Fibonacci_RootBoundary_cut

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem Algo2Lean.Fibonacci.Represented.delete_minimum :
    ∀ {state : Algo2Lean.Fibonacci.Snapshot} {forest : Algo2Lean.Fibonacci.Forest},
      Algo2Lean.Fibonacci.Represented state forest →
        Ne.{1} forest List.nil.{0} →
          Exists.{1} fun after =>
            Exists.{1} fun pending =>
              Exists.{1} fun promotions =>
                Algo2Lean.Fibonacci.DeleteMinimum state.minimum state after promotions ∧
                  Algo2Lean.Fibonacci.SplitRepresented after pending List.nil.{0} ∧
                    (∀ (degree : Int), LT.lt.{0} (after.table degree) (0 : Int)) ∧
                      List.Perm.{0}
                          (List.cons.{0} (Prod.mk.{0, 0} state.minimum (state.keys state.minimum))
                            pending.entries)
                          forest.entries ∧
                        Eq.{1} (HAdd.hAdd.{0, 0, 0} (List.length.{0} pending) (1 : Nat))
                            (HAdd.hAdd.{0, 0, 0} (List.length.{0} forest) promotions) ∧
                          LE.le.{0} pending.marks forest.marks ∧
                            LE.le.{0} promotions
                              (HAdd.hAdd.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0} (2 : Nat) (List.length.{0} forest.entries).log2)
                                (1 : Nat)) := by
  sorry
