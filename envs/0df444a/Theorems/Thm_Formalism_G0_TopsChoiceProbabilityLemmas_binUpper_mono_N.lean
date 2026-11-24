-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_binUpper_mono_N
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.binUpper_mono_N
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:50.586214+00:00
-- url     : https://prove2.me/theorems/129e632b-96b8-4bd5-b787-6a1da29b714f
-- title:
--   Tops Choice Probability Lemmas: bin Upper mono N
-- statement:
--   The Tops Choice Probability Lemmas construction uses the bin Upper mono N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L205-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L205-L211

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.binUpper_mono_N (G : ℕ) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (N : ℕ) :
    binUpper G δ N ≤ binUpper G δ (N - 1) := by sorry
