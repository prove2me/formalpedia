-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_idemSmall
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.idemSmall
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:25.5668+00:00
-- url     : https://prove2.me/theorems/984997f0-6654-48a4-bb7d-234986ef7cb7
-- title:
--   ring Data Objects: idem Small
-- statement:
--   The ring Data Objects construction uses the idem Small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/IdempotentImageSurjective.lean#L65-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/IdempotentImageSurjective.lean#L65-L82

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalModuleOf
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
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

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.idemSmall : StatIdemSmall := by sorry
