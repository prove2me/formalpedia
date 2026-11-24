-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_clearDen
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.clearDen
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:29:23.463478+00:00
-- url     : https://prove2.me/theorems/0d062eea-5504-4d7c-977c-6433085c884a
-- title:
--   ring Data Objects: clear Den
-- statement:
--   The ring Data Objects construction uses the clear Den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/DensityPointOfCornerSimple.lean#L142-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/DensityPointOfCornerSimple.lean#L142-L167

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
variable {O : Type} [CommRing O] [IsDomain O] {X : Type} (T : Subalgebra O (X → O)) {d : Type} [Fintype d]
  [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O))

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.clearDen (x : X) (A : Matrix d d (FractionRing O))
    (hA : A ∈ Submodule.span (FractionRing O)
      (Set.range fun g => (r g x).map (algebraMap O (FractionRing O)))) :
    ∃ b : O, b ≠ 0 ∧ ∃ a ∈ tSpan T r,
      (a x).map (algebraMap O (FractionRing O)) = algebraMap O (FractionRing O) b • A := by sorry
