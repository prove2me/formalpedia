-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_cell_eq
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.cell_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:31:07.211141+00:00
-- url     : https://prove2.me/theorems/7bedf93b-a164-49af-a273-e4a4c7c1138e
-- title:
--   Tops Choice Probability Lemmas: cell eq
-- statement:
--   The Tops Choice Probability Lemmas construction uses the cell eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L224-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L224-L231

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.cell_eq {r u s c : ℕ} (hc : 1 ≤ c) :
    cell r u s c = Ico (s * ((6 * r + 1) * u) + (c - 1) * u)
      (s * ((6 * r + 1) * u) + (c - 1) * u + u) := by sorry
