-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_marked_iff
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.marked_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:09.596864+00:00
-- url     : https://prove2.me/theorems/147585fe-e548-46f2-b26a-0fc33f9dc4ff
-- title:
--   Tops Choice Probability Lemmas: marked iff
-- statement:
--   The Tops Choice Probability Lemmas construction uses the marked iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L280-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L280-L283

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.marked_iff (t : Finset ℕ) (r u s : ℕ) :
    Marked t r u s ↔ ∀ c ∈ Icc 1 (6 * r + 1), EC r u s c t := by sorry
