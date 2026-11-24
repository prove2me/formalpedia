-- Prove2me | Theorems.Thm_Formalism_G0_tail_concavity
-- name    : Formalism.G0.tail_concavity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:03.458476+00:00
-- url     : https://prove2.me/theorems/e1d75250-a353-4c4f-8b23-a141405ebb25
-- title:
--   G0: tail concavity
-- statement:
--   The G0 construction uses the tail concavity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailConcavity.lean#L118-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailConcavity.lean#L118-L240

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailConcavity
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
open Finset
open Formalism.G0.TailConcavityP

theorem Formalism.G0.tail_concavity : TailConcavity := by sorry
