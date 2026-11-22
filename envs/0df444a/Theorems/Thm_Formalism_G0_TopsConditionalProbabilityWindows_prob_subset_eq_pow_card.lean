-- Prove2me | Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_prob_subset_eq_pow_card
-- name    : Formalism.G0.TopsConditionalProbabilityWindows.prob_subset_eq_pow_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:43.814298+00:00
-- url     : https://prove2.me/theorems/128cc4f7-9370-4e85-866e-648e82a70bda
-- title:
--   Tops Conditional Probability Windows: prob subset eq pow card
-- statement:
--   The Tops Conditional Probability Windows construction uses the prob subset eq pow card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L78-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L78-L105

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
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
open Formalism.G0.TopsConditionalProbabilityWindows

theorem Formalism.G0.TopsConditionalProbabilityWindows.prob_subset_eq_pow_card {U S : Finset ℕ} (δ : ℝ) (hS : S ⊆ U) :
    P U δ (fun t => S ⊆ t) = δ ^ S.card := by sorry
