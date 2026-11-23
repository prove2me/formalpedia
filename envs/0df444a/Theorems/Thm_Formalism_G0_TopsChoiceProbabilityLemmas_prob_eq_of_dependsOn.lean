-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_eq_of_dependsOn
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.prob_eq_of_dependsOn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:38.092847+00:00
-- url     : https://prove2.me/theorems/fba8d151-46cb-45f4-9453-9e72ea1a87ca
-- title:
--   Tops Choice Probability Lemmas: prob eq of depends On
-- statement:
--   The Tops Choice Probability Lemmas construction uses the prob eq of depends On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L90-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L90-L95

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.prob_eq_of_dependsOn {U S : Finset ℕ} (δ : ℝ) (hS : S ⊆ U) {A : Finset ℕ → Prop} (hA : Dep S A) :
    P U δ A = P S δ A := by sorry
