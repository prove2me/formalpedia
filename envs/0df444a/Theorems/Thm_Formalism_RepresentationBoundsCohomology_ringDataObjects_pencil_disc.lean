-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_pencil_disc
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.pencil_disc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:34.111278+00:00
-- url     : https://prove2.me/theorems/e18718a8-1eaa-4ab6-b0b5-7cf769554d2d
-- title:
--   ring Data Objects: pencil disc
-- statement:
--   The ring Data Objects construction uses the pencil disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/DensityPointOfCornerSimple.lean#L46-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/DensityPointOfCornerSimple.lean#L46-L72

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

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.pencil_disc {K : Type*} [Field K] {S : Type*} [Fintype S] [DecidableEq S] (B0 B1 : Matrix S S K)
    (h : B1.charpoly.Separable) :
    ∃ D : Polynomial K, D ≠ 0 ∧ ∀ c, D.eval c ≠ 0 → (c • B0 + B1).charpoly.Separable := by sorry
