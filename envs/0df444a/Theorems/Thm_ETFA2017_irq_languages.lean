-- Prove2me | Theorems.Thm_ETFA2017_irq_languages
-- name    : ETFA2017.irq_languages
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-24T06:51:49.700582+00:00
-- url     : https://prove2.me/theorems/86a935f8-8ccc-4e87-a48d-e50035134707
-- title:
--   The full component product and Figure 11(g) recognize the same traces
-- statement:
--   For every finite IRQ word, generated-language membership agrees between the synchronous product and Figure 11(g). Marked-language membership agrees as well.
-- source:
--   D. B. de Oliveira, R. S. de Oliveira, T. Cucinotta and L. Abeni, ETFA 2017, Automata-Based Modeling of Interrupts in the Linux PREEMPT RT Kernel.  https://retis.santannapisa.it/~tommaso/publications/ETFA-2017.pdf#page=7

import Definitions.Def_ETFA2017_IRQFigure
open RamadgeWonham.Shared

namespace ETFA2017
theorem irq_languages (w : List IRQEvent) :
    (w ∈ irqComponents.L ↔ w ∈ irqFigure.L) ∧ (w ∈ irqComponents.Lm ↔ w ∈ irqFigure.Lm) := by sorry
end ETFA2017
