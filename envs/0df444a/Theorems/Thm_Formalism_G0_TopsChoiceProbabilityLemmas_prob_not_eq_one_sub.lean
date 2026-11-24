-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_not_eq_one_sub
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.prob_not_eq_one_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:54.790808+00:00
-- url     : https://prove2.me/theorems/3c7e1bb2-c69b-4b96-8ce6-de7a3458481a
-- title:
--   Tops Choice Probability Lemmas: prob not eq one sub
-- statement:
--   The Tops Choice Probability Lemmas construction uses the prob not eq one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L142-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L142-L150

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.prob_not_eq_one_sub (U : Finset ℕ) (δ : ℝ) (A : Finset ℕ → Prop) :
    P U δ (fun t => ¬ A t) = 1 - P U δ A := by sorry
