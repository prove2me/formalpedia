-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_w_union
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.w_union
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:59.253433+00:00
-- url     : https://prove2.me/theorems/03b916b0-82d6-48f0-aa57-d2c4bbae939a
-- title:
--   Tops Choice Probability Lemmas: w union
-- statement:
--   The Tops Choice Probability Lemmas construction uses the w union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L35-L44

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.w_union {S R a b : Finset ℕ} (δ : ℝ) (h : Disjoint S R) (ha : a ⊆ S) (hb : b ⊆ R) :
    δ ^ (a ∪ b).card * (1 - δ) ^ ((S ∪ R).card - (a ∪ b).card) =
      (δ ^ a.card * (1 - δ) ^ (S.card - a.card)) * (δ ^ b.card * (1 - δ) ^ (R.card - b.card)) := by sorry
