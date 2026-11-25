-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_ontoSpan
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.ontoSpan
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:20.54729+00:00
-- url     : https://prove2.me/theorems/f57a0470-d23b-58ee-92c7-77a57b870956
-- title:
--   ring Data Objects: onto Span
-- statement:
--   The ring Data Objects construction uses the onto Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/BurnsideMat.lean#L69-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/BurnsideMat.lean#L69-L70

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CharpolyRevMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IdemNormalForm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AbsolutelyIrreducibleSpan
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_BurnsideMat
import Theorems.Thm_UpperTheory_Reformulated_B_AbsolutelyIrreducibleSpan_ontoSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.ontoSpan : StatOntoSpan := by sorry
