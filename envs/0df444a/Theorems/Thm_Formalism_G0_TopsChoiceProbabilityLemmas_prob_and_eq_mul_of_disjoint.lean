-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_and_eq_mul_of_disjoint
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.prob_and_eq_mul_of_disjoint
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:17.781647+00:00
-- url     : https://prove2.me/theorems/d6d525c5-47e0-4e4f-af84-108a0449a056
-- title:
--   Tops Choice Probability Lemmas: prob and eq mul of disjoint
-- statement:
--   The Tops Choice Probability Lemmas construction uses the prob and eq mul of disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L46-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L46-L65

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.prob_and_eq_mul_of_disjoint (S R : Finset ℕ) (δ : ℝ) (h : Disjoint S R) (A B : Finset ℕ → Prop) :
    P (S ∪ R) δ (fun t => A (t ∩ S) ∧ B (t ∩ R)) = P S δ A * P R δ B := by sorry
