-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_pencil_choose
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.pencil_choose
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:46.683156+00:00
-- url     : https://prove2.me/theorems/89e1fe69-e4bf-48bd-bad9-d7accbe39c44
-- title:
--   ring Data Objects: pencil choose
-- statement:
--   The ring Data Objects construction uses the pencil choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/DensityPointOfCornerSimple.lean#L112-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/DensityPointOfCornerSimple.lean#L112-L136

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdemFactor
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_DensityPointOfCornerSimple
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

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.pencil_choose {O : Type*} [CommRing O] [Infinite O] {K : Type*} [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) {S : Type*} [Fintype S] [DecidableEq S]
    (B0 B1 : Matrix S S K) (h : B1.charpoly.Separable) (c0 : K) (hc0 : c0 ≠ 0) :
    ∃ l : O, (B0 + (c0 * algebraMap O K l) • B1).charpoly.Separable := by sorry
