-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_even_card
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.even_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:56.589041+00:00
-- url     : https://prove2.me/theorems/5bf9d050-7162-4266-a24d-bf2aacf659ed
-- title:
--   Tops Choice Probability Lemmas: even card
-- statement:
--   The Tops Choice Probability Lemmas construction uses the even card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L268-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L268-L278

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.even_card (a u : ℕ) : u / 2 ≤ ((Ico a (a + u)).filter Even).card := by sorry
