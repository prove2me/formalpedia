-- Prove2me | Theorems.Thm_Formalism_G0_tops_choice_part_a
-- name    : Formalism.G0.tops_choice_part_a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:10.096996+00:00
-- url     : https://prove2.me/theorems/7d25c584-1600-4e65-a47e-cd1fc93055a7
-- title:
--   G0: tops choice part a
-- statement:
--   The G0 construction uses the tops choice part a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L202-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L202-L235

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open TopsConditionalProbabilityWindows

theorem Formalism.G0.tops_choice_part_a : TopsChoicePartA := by sorry
