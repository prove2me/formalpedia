-- Prove2me | Theorems.Thm_BitDFT_rewound_descriptor_correct
-- name    : BitDFT.rewound_descriptor_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:11:02.238226+00:00
-- url     : https://prove2.me/theorems/254a6efa-57f5-461e-bf5c-c4ec6445ca57
-- title:
--   Prepare two descriptor tapes from a source head at the end of its binary word
-- statement:
--   Given a binary descriptor y on the source tape, with its head immediately after the word and both destination tapes blank with heads at their markers, the combined machine prepares the two delimited descriptor tapes within 2|y|+6 transitions. Both target heads finish at the low-order end. The bound includes the rewind, the controller handoff, and the complete descriptor-copy routine. Source and parked native tape contents are preserved.
-- source:
--   Charged setup for the exact output scaler in the finite-precision DFT transfer mission.

import Definitions.Def_BitDFT_RewoundDescriptor
open BitDFT IntMul

theorem BitDFT.rewound_descriptor_correct (base : RewoundDescriptor.storage.Cfg) (y : List Bool) :
    ∃ t : ℕ, t ≤ 2*y.length+6 ∧
      RewoundDescriptor.machine.step^[t] (RewoundDescriptor.initial base y) =
        RewoundDescriptor.final base y := by sorry
