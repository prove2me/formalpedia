-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_detT
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.detT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:01.736447+00:00
-- url     : https://prove2.me/theorems/14ee97f4-4d57-4c34-a483-0e50f3b135ea
-- title:
--   ring Data Objects: det T
-- statement:
--   The ring Data Objects construction uses the det T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/CMemPolyT.lean#L74-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/CMemPolyT.lean#L74-L97

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

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.detT (hG1 : ∀ (g : G) (k : ℕ), (fun x => (Matrix.charpolyRev (r g x)).coeff k) ∈ T)
    (M : Xs → Matrix d d O[X]) (hM : M ∈ tSpan (polyT T) (rPoly r)) (k : ℕ) :
    (fun x => (M x).det.coeff k) ∈ T := by sorry
