-- Prove2me | Theorems.Thm_Formalism_G0_WalkSharpP_update_positionAt_base
-- name    : Formalism.G0.WalkSharpP.update_positionAt_base
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:52.42805+00:00
-- url     : https://prove2.me/theorems/9cf8c983-a857-4e82-97ef-6846b2e1aea3
-- title:
--   Walk Sharp P: update position At base
-- statement:
--   The Walk Sharp P construction uses the update position At base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L180-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/WalkSharp.lean#L180-L187

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
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
open Formalism.G0.WalkSharpP

theorem Formalism.G0.WalkSharpP.update_positionAt_base {V : ℕ} (B : Finset (Fin V)) (v : Fin V) :
    Function.update (vertexLabel B) v Slot.base = vertexLabel (B.erase v) := by sorry
