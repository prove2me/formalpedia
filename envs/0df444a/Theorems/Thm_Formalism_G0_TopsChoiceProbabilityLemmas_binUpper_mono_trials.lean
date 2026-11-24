-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_binUpper_mono_trials
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.binUpper_mono_trials
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:38.624113+00:00
-- url     : https://prove2.me/theorems/15215ade-546b-4f5d-9f10-5f576b700686
-- title:
--   Tops Choice Probability Lemmas: bin Upper mono trials
-- statement:
--   The Tops Choice Probability Lemmas construction uses the bin Upper mono trials property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L195-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L195-L203

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.binUpper_mono_trials {m G : ℕ} (h : m ≤ G) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (N : ℕ) :
    binUpper m δ N ≤ binUpper G δ N := by sorry
