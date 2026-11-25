-- Prove2me | Theorems.Thm_Formalism_G0_choice_of_tops_refined_holds
-- name    : Formalism.G0.choice_of_tops_refined_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:51.761919+00:00
-- url     : https://prove2.me/theorems/f9c0d7ee-02f7-4894-8417-024188a882ec
-- title:
--   G0: choice of tops refined holds
-- statement:
--   The G0 construction uses the choice of tops refined holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L590-L616
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L590-L616

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
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
open TopsChoiceProbabilityLemmas TopsConditionalProbabilityWindows

theorem Formalism.G0.choice_of_tops_refined_holds : TileConditionFailureProbBound := by sorry
