-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_card_insert_inter
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.card_insert_inter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:25:07.98296+00:00
-- url     : https://prove2.me/theorems/1c788771-7f54-41ee-91f1-7298c397a335
-- title:
--   Tops Choice Probability Lemmas: card insert inter
-- statement:
--   The Tops Choice Probability Lemmas construction uses the card insert inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L430-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L430-L442

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
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows

theorem Formalism.G0.TopsChoiceProbabilityLemmas.card_insert_inter (a : ℕ) (t W : Finset ℕ) :
    (insert a t ∩ W).card ≤ (t ∩ W.erase a).card + 1 := by sorry
