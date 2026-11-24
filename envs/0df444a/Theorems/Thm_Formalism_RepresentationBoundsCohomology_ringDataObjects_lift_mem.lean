-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_lift_mem
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.lift_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:49.818641+00:00
-- url     : https://prove2.me/theorems/a65e4e8a-8df0-40de-89e3-d8e477ffd49d
-- title:
--   ring Data Objects: lift mem
-- statement:
--   The ring Data Objects construction uses the lift mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/CMemPolyT.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/CMemPolyT.lean#L55-L61

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_RingDataObjects
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CMemPolyT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical Polynomial
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
variable {O : Type} [CommRing O] {Xs : Type} (T : Subalgebra O (Xs → O))
  {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (Xs → Matrix d d O))

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.lift_mem {a : Xs → Matrix d d O} (ha : a ∈ tSpan T r) :
    (fun x => (a x).map C) ∈ tSpan (polyT T) (rPoly r) := by sorry
