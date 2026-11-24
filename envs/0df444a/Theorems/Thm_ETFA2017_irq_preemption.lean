-- Prove2me | Theorems.Thm_ETFA2017_irq_preemption
-- name    : ETFA2017.irq_preemption
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-24T06:53:17.1128+00:00
-- url     : https://prove2.me/theorems/c6c50d9a-16b7-4771-ae40-cccea46e4a28
-- title:
--   Same-CPU handler exclusion and NMI preemption
-- statement:
--   If two distinct vectors on the same CPU both accept their projected prefix and one handler is active, the second handler is inactive and cannot enter. A complete routed execution witnesses NMI handling inside an IRQ handler. A separate printed path witnesses hardware IRQ arrival during NMI execution.
-- source:
--   D. B. de Oliveira, R. S. de Oliveira, T. Cucinotta and L. Abeni, ETFA 2017, Automata-Based Modeling of Interrupts in the Linux PREEMPT RT Kernel.  https://retis.santannapisa.it/~tommaso/publications/ETFA-2017.pdf#page=6

import Definitions.Def_ETFA2017_Checker
import Definitions.Def_ETFA2017_IRQFigure
open RamadgeWonham.Shared

namespace ETFA2017
theorem irq_preemption :
    (∀ {cpus vectors : Nat} (w : List (SystemEvent cpus vectors)) (cpu : Fin cpus)
      (i j : Fin vectors) (p q : Fin 38), i ≠ j →
      irqFigure.run (w.filterMap (irqView cpu i)) = some p →
      irqFigure.run (w.filterMap (irqView cpu j)) = some q → inIRQHandler p = true →
      inIRQHandler q = false ∧ figureStep .irqEntry q = none) ∧
    (let w : List (SystemEvent 1 1) := [.irqRequest 0 0, .hwDisable 0 0, .irqEntry 0 0,
      .nmiRequest 0, .nmiEntry 0, .nmiExit 0, .irqExit 0 0]
     ((interruptSystem nmiFigure irqFigure).run w).isSome = true) ∧
    (figureStep .nmiEntry 7 = some 8 ∧ figureStep .irq 8 = some 18 ∧
      figureStep .irqEntry 8 = none ∧ figureStep .nmiExit 18 = some 14) := by sorry
end ETFA2017
