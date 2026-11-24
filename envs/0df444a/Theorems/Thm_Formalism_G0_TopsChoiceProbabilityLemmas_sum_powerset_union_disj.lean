-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_sum_powerset_union_disj
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.sum_powerset_union_disj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:56.360566+00:00
-- url     : https://prove2.me/theorems/011e1c2e-2a2a-4990-9bbd-d9a933453a25
-- title:
--   Tops Choice Probability Lemmas: sum powerset union disj
-- statement:
--   The Tops Choice Probability Lemmas construction uses the sum powerset union disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L16-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L16-L33

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.sum_powerset_union_disj {β : Type*} [AddCommMonoid β] (S R : Finset ℕ)
    (h : Disjoint S R) (F : Finset ℕ → β) :
    ∑ t ∈ (S ∪ R).powerset, F t = ∑ a ∈ S.powerset, ∑ b ∈ R.powerset, F (a ∪ b) := by sorry
