-- Prove2me | Theorems.Thm_FibonacciModuleAnalysis_consolidate_from_forest
-- name    : FibonacciModuleAnalysis.consolidate_from_forest
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:56:43.690749+00:00
-- url     : https://prove2.me/theorems/094c9f70-30ef-4805-9bf3-9ec3cd4e014a
-- title:
--   Fibonacci heap: compiled consolidation with exact source-clock costs
-- statement:
--   Given a valid layout, a represented finite pending forest F and an empty scratch table, the compiled consolidation Call returns a represented queue with the same entries and marks. Let r be the original root count, l the links, s the degree scans and c the final comparisons. The result has r-l roots; its root count and s are at most 2 floor(log₂ |entries(F)|)+2, and c is at most its root count. Exact increments are r root scans, l+c comparisons, l links and s degree scans.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_heap.lean#L4220-L4276

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_add_root_summary
import Theorems.Thm_FibonacciModuleAnalysis_link_summary
import Theorems.Thm_FibonacciModuleAnalysis_realize_root_consumption
import Theorems.Thm_Algo2Lean_Fibonacci_SplitRepresented_consume_roots

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciModuleAnalysis.consolidate_from_forest :
    ∀ (heap : Algo2LeanGenerated.Heap)
      (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
      (layout : FibonacciModuleAnalysis.Layout),
      layout.Valid heap queue →
        ∀ (forest : Algo2Lean.Fibonacci.Forest),
          Algo2Lean.Fibonacci.SplitRepresented (FibonacciModuleAnalysis.snapshot heap layout) forest
              List.nil.{0} →
            (∀ (degree : Int), LT.lt.{0} (heap.read layout.table degree) (0 : Int)) →
              Exists.{1} fun finalHeap =>
                Exists.{1} fun finalLayout =>
                  Exists.{1} fun afterForest =>
                    Exists.{1} fun links =>
                      Exists.{1} fun scans =>
                        Exists.{1} fun comparisons =>
                          Algo.fibonacci_heap.FibonacciHeap.consolidate.Call heap queue finalHeap () ∧
                            FibonacciModuleAnalysis.ConsumeEffect queue heap layout (-1 : Int) finalHeap
                                finalLayout (List.length.{0} forest) links ∧
                              FibonacciModuleAnalysis.QueueRep finalHeap queue finalLayout afterForest ∧
                                List.Perm.{0} afterForest.entries forest.entries ∧
                                  Eq.{1} afterForest.marks forest.marks ∧
                                    Eq.{1} (HAdd.hAdd.{0, 0, 0} links (List.length.{0} afterForest))
                                        (List.length.{0} forest) ∧
                                      LE.le.{0} (List.length.{0} afterForest)
                                          (HAdd.hAdd.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0} (2 : Nat)
                                              (List.length.{0} forest.entries).log2)
                                            (2 : Nat)) ∧
                                        LE.le.{0} scans
                                            (HAdd.hAdd.{0, 0, 0}
                                              (HMul.hMul.{0, 0, 0} (2 : Nat)
                                                (List.length.{0} forest.entries).log2)
                                              (2 : Nat)) ∧
                                          LE.le.{0} comparisons (List.length.{0} afterForest) ∧
                                            Eq.{1} (heap.cost finalHeap) fun clock =>
                                              HAdd.hAdd.{0, 0, 0}
                                                (HAdd.hAdd.{0, 0, 0}
                                                  (HAdd.hAdd.{0, 0, 0}
                                                    (Algo2LeanGenerated.Clocks.single "heap_root_scans"
                                                      (List.length.{0} forest) clock)
                                                    (Algo2LeanGenerated.Clocks.single "heap_comparisons"
                                                      (HAdd.hAdd.{0, 0, 0} links comparisons) clock))
                                                  (Algo2LeanGenerated.Clocks.single "heap_links" links
                                                    clock))
                                                (Algo2LeanGenerated.Clocks.single "heap_degree_scans"
                                                  scans clock) := by
  sorry
