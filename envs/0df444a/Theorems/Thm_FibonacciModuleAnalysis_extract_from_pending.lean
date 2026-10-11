-- Prove2me | Theorems.Thm_FibonacciModuleAnalysis_extract_from_pending
-- name    : FibonacciModuleAnalysis.extract_from_pending
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T00:00:54.826044+00:00
-- url     : https://prove2.me/theorems/b832b0ad-275e-44c4-87b6-1de706ffcbf6
-- title:
--   Fibonacci heap: complete a minimum deletion by verified consolidation
-- statement:
--   Assume a valid layout whose explicit remove-minimum heap has a represented pending forest and empty scratch table. There is a final extraction effect and represented queue with exactly the pending entries and marks. The theorem carries root/link identities, logarithmic scan bounds, preservation outside the queue, unchanged layout references, and exact consolidation clock increments. The premise describes the state after local minimum removal; it is discharged by the structural deletion theorem.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_heap.lean#L5206-L5266

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_consolidate_from_forest

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciModuleAnalysis.extract_from_pending :
    ∀ (heap : Algo2LeanGenerated.Heap)
      (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
      (layout : FibonacciModuleAnalysis.Layout),
      layout.Valid heap queue →
        ∀ (vertex : Int) (pending : Algo2Lean.Fibonacci.Forest),
          Algo2Lean.Fibonacci.SplitRepresented
              (FibonacciModuleAnalysis.snapshot
                (FibonacciModuleAnalysis.removeMinimumHeap heap queue layout vertex)
                (FibonacciModuleAnalysis.removeMinimumLayout heap layout vertex))
              pending List.nil.{0} →
            (∀ (degree : Int),
                LT.lt.{0}
                  ((FibonacciModuleAnalysis.removeMinimumHeap heap queue layout vertex).read
                    layout.table degree)
                  (0 : Int)) →
              Exists.{1} fun after =>
                Exists.{1} fun finalLayout =>
                  Exists.{1} fun forest =>
                    Exists.{1} fun links =>
                      Exists.{1} fun scans =>
                        Exists.{1} fun comparisons =>
                          FibonacciModuleAnalysis.ExtractionEffect queue vertex heap layout after
                              finalLayout ∧
                            FibonacciModuleAnalysis.QueueRep after queue finalLayout forest ∧
                              List.Perm.{0} forest.entries pending.entries ∧
                                Eq.{1} forest.marks pending.marks ∧
                                  Eq.{1} (HAdd.hAdd.{0, 0, 0} links (List.length.{0} forest))
                                      (List.length.{0} pending) ∧
                                    LE.le.{0} (List.length.{0} forest)
                                        (HAdd.hAdd.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0} (2 : Nat)
                                            (List.length.{0} pending.entries).log2)
                                          (2 : Nat)) ∧
                                      LE.le.{0} scans
                                          (HAdd.hAdd.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0} (2 : Nat)
                                              (List.length.{0} pending.entries).log2)
                                            (2 : Nat)) ∧
                                        LE.le.{0} comparisons (List.length.{0} forest) ∧
                                          heap.Modifies after layout.refs
                                              (List.cons.{0} queue List.nil.{0}) ∧
                                            Eq.{1} finalLayout.refs layout.refs ∧
                                              ∀ (clock : String),
                                                Eq.{1} (after.clocks clock)
                                                  (HAdd.hAdd.{0, 0, 0}
                                                    (HAdd.hAdd.{0, 0, 0}
                                                      (HAdd.hAdd.{0, 0, 0}
                                                        (HAdd.hAdd.{0, 0, 0} (heap.clocks clock)
                                                          (Algo2LeanGenerated.Clocks.single
                                                            "heap_root_scans" (List.length.{0} pending)
                                                            clock))
                                                        (Algo2LeanGenerated.Clocks.single
                                                          "heap_comparisons"
                                                          (HAdd.hAdd.{0, 0, 0} links comparisons)
                                                          clock))
                                                      (Algo2LeanGenerated.Clocks.single "heap_links"
                                                        links clock))
                                                    (Algo2LeanGenerated.Clocks.single
                                                      "heap_degree_scans" scans clock)) := by
  sorry
