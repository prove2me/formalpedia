-- Prove2me | Theorems.Thm_Formalism_G0_MarkedRunP_mem_cell_succ
-- name    : Formalism.G0.MarkedRunP.mem_cell_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:37.359063+00:00
-- url     : https://prove2.me/theorems/7b5de674-ba34-471a-8d07-18512ae18a3a
-- title:
--   Marked Run P: mem cell succ
-- statement:
--   The Marked Run P construction uses the mem cell succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/MarkedRun.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/MarkedRun.lean#L7-L10

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_MarkedRun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.MarkedRunP

theorem Formalism.G0.MarkedRunP.mem_cell_succ (r u s q x : ℕ) :
    x ∈ cell r u s (q + 1) ↔
      s * ((6 * r + 1) * u) + q * u ≤ x ∧ x < s * ((6 * r + 1) * u) + q * u + u := by sorry
