-- Prove2me | Theorems.Thm_ETFA2017_interrupt_trace_correct
-- name    : ETFA2017.interrupt_trace_correct
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-24T06:55:26.829098+00:00
-- url     : https://prove2.me/theorems/fd86ae44-e48f-46b0-80b5-8e9ecb83f278
-- title:
--   The modular trace checker agrees with both published interrupt automata
-- statement:
--   For any finite number of CPUs and IRQ vectors and every ordered trace of modeled events, the checker using the component generators succeeds exactly when every CPU projection is legal in Figure 7 and every CPU/vector IRQ projection is legal in Figure 11(g).
-- source:
--   D. B. de Oliveira, R. S. de Oliveira, T. Cucinotta and L. Abeni, ETFA 2017, Automata-Based Modeling of Interrupts in the Linux PREEMPT RT Kernel.  https://retis.santannapisa.it/~tommaso/publications/ETFA-2017.pdf#page=4

import Definitions.Def_ETFA2017_Checker
import Definitions.Def_ETFA2017_IRQFigure
open RamadgeWonham.Shared

namespace ETFA2017
theorem interrupt_trace_correct {cpus vectors : Nat} (w : List (SystemEvent cpus vectors)) :
    (∃ q, checkTrace nmiComponents irqComponents w = .ok q) ↔
      (∀ c, w.filterMap (nmiView c) ∈ nmiFigure.L) ∧
      (∀ c v, w.filterMap (irqView c v) ∈ irqFigure.L) := by sorry
end ETFA2017
