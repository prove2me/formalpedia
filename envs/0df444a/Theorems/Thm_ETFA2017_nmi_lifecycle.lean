-- Prove2me | Theorems.Thm_ETFA2017_nmi_lifecycle
-- name    : ETFA2017.nmi_lifecycle
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-24T06:38:15.356202+00:00
-- url     : https://prove2.me/theorems/5c379023-3388-4fad-825b-17dd4faaa3f0
-- title:
--   The NMI product, its reachable phases and its two languages
-- statement:
--   For every NMI trace, the component product reaches exactly the corresponding Figure 7 phase. Its generated language consists of prefixes of repeated request–entry–exit cycles, and its marked language consists of complete cycles.
-- source:
--   D. B. de Oliveira, R. S. de Oliveira, T. Cucinotta and L. Abeni, ETFA 2017, Automata-Based Modeling of Interrupts in the Linux PREEMPT RT Kernel.  https://retis.santannapisa.it/~tommaso/publications/ETFA-2017.pdf#page=5

import Definitions.Def_ETFA2017_NMI
open RamadgeWonham.Shared

namespace ETFA2017
theorem nmi_lifecycle (w : List NMIEvent) :
    nmiComponents.run w = (nmiFigure.run w).map NMIPhase.components ∧
    (w ∈ nmiComponents.L ↔ ∃ n, List.IsPrefix w (nmiCycles n)) ∧
    (w ∈ nmiComponents.Lm ↔ ∃ n, w = nmiCycles n) := by sorry
end ETFA2017
