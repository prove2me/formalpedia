-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_le_card_eq_binUpper
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.prob_le_card_eq_binUpper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:25:10.210806+00:00
-- url     : https://prove2.me/theorems/57f5355b-76a8-4aac-9fbc-c79d47658962
-- title:
--   Tops Choice Probability Lemmas: prob le card eq bin Upper
-- statement:
--   The Tops Choice Probability Lemmas construction uses the prob le card eq bin Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L175-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L175-L193

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.prob_le_card_eq_binUpper (S : Finset ℕ) (δ : ℝ) (N : ℕ) :
    P S δ (fun a => N ≤ a.card) = binUpper S.card δ N := by sorry
