-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_listDiag
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.listDiag
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:29:14.415853+00:00
-- url     : https://prove2.me/theorems/a7cbb31e-07d7-4b28-a8a3-e25ed9151a52
-- title:
--   ring Data Objects: list Diag
-- statement:
--   The ring Data Objects construction uses the list Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/CharpolyRevMap.lean#L100-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/CharpolyRevMap.lean#L100-L106

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

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.listDiag {A : Type*} [CommRing A] {d : Type*} [Fintype d] [DecidableEq d] (f : ℕ → d → A)
    (l : List ℕ) :
    (l.map fun i => (Matrix.diagonal (f i) : Matrix d d A)).prod =
      Matrix.diagonal fun a => (l.map fun i => f i a).prod := by sorry
