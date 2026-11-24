-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_marked_insert
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.marked_insert
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:43.217385+00:00
-- url     : https://prove2.me/theorems/c569bd8b-9052-42ec-87bf-d5bfeef3d5ab
-- title:
--   Tops Choice Probability Lemmas: marked insert
-- statement:
--   The Tops Choice Probability Lemmas construction uses the marked insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L317-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L317-L326

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.marked_insert (t : Finset ℕ) {r u s i₀ : ℕ} (hnot : i₀ ∉ tile r u s) :
    Marked (insert i₀ t) r u s ↔ Marked t r u s := by sorry
