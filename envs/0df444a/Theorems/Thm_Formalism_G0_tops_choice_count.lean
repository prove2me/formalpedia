-- Prove2me | Theorems.Thm_Formalism_G0_tops_choice_count
-- name    : Formalism.G0.tops_choice_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:03.8698+00:00
-- url     : https://prove2.me/theorems/d15b16bb-b6d2-4beb-8b11-9c6d1f6806c8
-- title:
--   G0: tops choice count
-- statement:
--   The G0 construction uses the tops choice count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoiceCount.lean#L112-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoiceCount.lean#L112-L120

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoiceCount
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
open Formalism Formalism.G0
open TopsCount

theorem Formalism.G0.tops_choice_count : SmallCardCondProbBound := by sorry
