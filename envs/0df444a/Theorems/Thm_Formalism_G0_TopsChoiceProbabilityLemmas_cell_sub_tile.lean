-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_cell_sub_tile
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.cell_sub_tile
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:31.580019+00:00
-- url     : https://prove2.me/theorems/e7a3a78e-3513-4552-a478-d16723bcf7d8
-- title:
--   Tops Choice Probability Lemmas: cell sub tile
-- statement:
--   The Tops Choice Probability Lemmas construction uses the cell sub tile property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L237-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L237-L245

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.cell_sub_tile {r u s c : ℕ} (hc : 1 ≤ c) (hc' : c ≤ 6 * r + 1) :
    cell r u s c ⊆ tile r u s := by sorry
