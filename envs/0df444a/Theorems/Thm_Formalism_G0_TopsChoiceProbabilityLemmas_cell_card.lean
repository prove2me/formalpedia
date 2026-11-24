-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_cell_card
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.cell_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:56.66585+00:00
-- url     : https://prove2.me/theorems/fc3412d3-a9e3-4106-8dbb-00ab042dca65
-- title:
--   Tops Choice Probability Lemmas: cell card
-- statement:
--   The Tops Choice Probability Lemmas construction uses the cell card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L233-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L233-L235

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.cell_card {r u s c : ℕ} (hc : 1 ≤ c) : (cell r u s c).card = u := by sorry
