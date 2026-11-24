-- Prove2me | Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_tile_div
-- name    : Formalism.G0.TopsChoiceProbabilityLemmas.tile_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:03.867796+00:00
-- url     : https://prove2.me/theorems/7b319cab-14c2-495a-b058-8b65feefb935
-- title:
--   Tops Choice Probability Lemmas: tile div
-- statement:
--   The Tops Choice Probability Lemmas construction uses the tile div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L301-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L301-L304

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

theorem Formalism.G0.TopsChoiceProbabilityLemmas.tile_div {r u s x : ℕ} (h : x ∈ tile r u s) : x / ((6 * r + 1) * u) = s := by sorry
