-- Prove2me | Theorems.Thm_ETFA2017_observedTrace_iff
-- name    : ETFA2017.observedTrace_iff
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-24T06:54:46.667448+00:00
-- url     : https://prove2.me/theorems/6ae54bb4-331b-4272-820a-b13e4457105f
-- title:
--   Observation extension for unrecorded hardware requests
-- statement:
--   A sequence can be read by the silent-step observation semantics exactly when a complete modeled event word passes the checker and erasing hardware requests yields that sequence. CPU and vector identifiers and the relative order of visible events are preserved.
-- source:
--   D. B. de Oliveira, R. S. de Oliveira, T. Cucinotta and L. Abeni, ETFA 2017, Automata-Based Modeling of Interrupts in the Linux PREEMPT RT Kernel.  https://retis.santannapisa.it/~tommaso/publications/ETFA-2017.pdf#page=3

import Definitions.Def_ETFA2017_Checker
open RamadgeWonham.Shared

namespace ETFA2017
variable {cpus vectors : Nat} (N : Generator NMIEvent) (I : Generator IRQEvent)
theorem observedTrace_iff (obs : List (SystemEvent cpus vectors)) :
    (∃ q, Observes (interruptSystem N I) recorded (interruptSystem N I).q0 obs q) ↔
      ∃ w, w.filter recorded = obs ∧ ∃ q, checkTrace N I w = .ok q := by sorry
end ETFA2017
