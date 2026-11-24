-- Prove2me | Theorems.Thm_ETFA2017_irq_masking
-- name    : ETFA2017.irq_masking
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-24T06:50:55.810666+00:00
-- url     : https://prove2.me/theorems/cd201437-469e-40d7-8288-d06d52708635
-- title:
--   Hardware masking and handler entry in the IRQ product
-- statement:
--   For a tuple of twelve component states, characterize exactly when hardware can take the local mask on behalf of this vector and when its handler can enter. Each condition lists the controlling local coordinates.
-- source:
--   D. B. de Oliveira, R. S. de Oliveira, T. Cucinotta and L. Abeni, ETFA 2017, Automata-Based Modeling of Interrupts in the Linux PREEMPT RT Kernel.  https://retis.santannapisa.it/~tommaso/publications/ETFA-2017.pdf#page=7

import Definitions.Def_ETFA2017_IRQComponents
open RamadgeWonham.Shared
open ETFA2017.IRQEvent

namespace ETFA2017
theorem irq_masking (hardware handler localMask vector gate pending lifecycle repeatIRQ
    vectorGate nmi context mask : Nat) :
    let q := [hardware, handler, localMask, vector, gate, pending, lifecycle, repeatIRQ,
              vectorGate, nmi, context, mask]
    ((componentStep hwDisable q).isSome = true ↔
      localMask = 0 ∧ gate = 0 ∧ pending = 2 ∧ lifecycle = 0 ∧ vectorGate = 0 ∧
      nmi = 0 ∧ context = 0) ∧
    ((componentStep irqEntry q).isSome = true ↔
      handler = 0 ∧ gate = 2 ∧ lifecycle = 2 ∧ nmi = 0 ∧ context = 1 ∧ mask = 2) := by sorry
end ETFA2017
