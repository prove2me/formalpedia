-- Prove2me | Theorems.Thm_Formalism_G0_det_divides
-- name    : Formalism.G0.det_divides
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:54.470087+00:00
-- url     : https://prove2.me/theorems/fa093ac2-6c72-4c80-8913-abf2d2f4f1bc
-- title:
--   G0: det divides
-- statement:
--   The G0 construction uses the det divides property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L730-L738
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L730-L738

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0

theorem Formalism.G0.det_divides : DetDivides := by sorry
