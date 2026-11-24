-- Prove2me | Theorems.Thm_Formalism_G0_all_but_le_smith
-- name    : Formalism.G0.all_but_le_smith
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:07.000548+00:00
-- url     : https://prove2.me/theorems/14402f57-763c-4ac9-baea-d202cbb0d36b
-- title:
--   G0: all but le smith
-- statement:
--   The G0 construction uses the all but le smith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/AllButLESmith.lean#L195-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/AllButLESmith.lean#L195-L198

import Definitions.Def_Formalism_SubspaceCounting_StatementD
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_AllButLESmith
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
open Module
open Formalism Formalism.G0

theorem Formalism.G0.all_but_le_smith : AllButLESmith := by sorry
