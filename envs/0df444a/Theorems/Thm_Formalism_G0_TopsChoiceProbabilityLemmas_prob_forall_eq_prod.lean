-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_prob_forall_eq_prod
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.prob_forall_eq_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:24.324256+00:00
-- url     : https://prove2.me/theorems/12c08dcb-93da-4295-929b-7ad39354524c
-- title:
--   Tops Choice Probability Lemmas: prob forall eq prod
-- statement:
--   The Tops Choice Probability Lemmas construction uses the prob forall eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L112-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L112-L140

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.prob_forall_eq_prod {ι : Type*} [DecidableEq ι] {U : Finset ℕ} (δ : ℝ) (F : Finset ι)
    (S : ι → Finset ℕ) (hS : ∀ i ∈ F, S i ⊆ U)
    (hd : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (E : ι → Finset ℕ → Prop) (hE : ∀ i ∈ F, Dep (S i) (E i)) :
    P U δ (fun t => ∀ i ∈ F, E i t) = ∏ i ∈ F, P U δ (E i) := by sorry
