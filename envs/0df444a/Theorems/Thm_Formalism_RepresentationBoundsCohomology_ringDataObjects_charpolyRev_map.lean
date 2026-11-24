-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_charpolyRev_map
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.charpolyRev_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:30:25.381448+00:00
-- url     : https://prove2.me/theorems/cd64dfdd-fbbd-48ef-abce-fc2ee757c56c
-- title:
--   ring Data Objects: charpoly Rev map
-- statement:
--   The ring Data Objects construction uses the charpoly Rev map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/CharpolyRevMap.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/CharpolyRevMap.lean#L42-L49

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CharpolyRevMap
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

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.charpolyRev_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {d : Type*} [Fintype d]
    [DecidableEq d] (M : Matrix d d A) :
    (Matrix.charpolyRev M).map f = Matrix.charpolyRev (M.map f) := by sorry
