-- Prove2me | Theorems.Thm_ETFA2017_checkTrace_first_failure
-- name    : ETFA2017.checkTrace_first_failure
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-24T06:54:04.654032+00:00
-- url     : https://prove2.me/theorems/c33860b8-e3c0-49d5-9eb0-a639404ebf19
-- title:
--   The first failing event and its participating slot
-- statement:
--   For any NMI and IRQ generators and any decomposition into a prefix, event and suffix, the checker reports the prefix length exactly when every slot accepts its projected prefix and some participating slot then has an undefined transition.
-- source:
--   D. B. de Oliveira, R. S. de Oliveira, T. Cucinotta and L. Abeni, ETFA 2017, Automata-Based Modeling of Interrupts in the Linux PREEMPT RT Kernel.  https://retis.santannapisa.it/~tommaso/publications/ETFA-2017.pdf#page=4

import Definitions.Def_ETFA2017_Checker
open RamadgeWonham.Shared

namespace ETFA2017
variable {cpus vectors : Nat} (N : Generator NMIEvent) (I : Generator IRQEvent)
theorem checkTrace_first_failure (pre : List (SystemEvent cpus vectors)) (e : SystemEvent cpus vectors)
    (post : List (SystemEvent cpus vectors)) :
    checkTrace N I (pre ++ e :: post) = .error pre.length ↔
      (∀ s : Slot cpus vectors, pre.filterMap (route s) ∈ (slotModel N I s).L) ∧
      ∃ (s : Slot cpus vectors) (a : s.Alphabet) (q : (slotModel N I s).Q), route s e = some a ∧
        (slotModel N I s).run (pre.filterMap (route s)) = some q ∧
        (slotModel N I s).δ a q = none := by sorry
end ETFA2017
