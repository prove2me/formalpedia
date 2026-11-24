-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_blockDiag_of_mem
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.blockDiag_of_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:28:22.352548+00:00
-- url     : https://prove2.me/theorems/14b1cff6-1839-4013-825f-5b705fde2b1d
-- title:
--   ring Data Objects: block Diag of mem
-- statement:
--   The ring Data Objects construction uses the block Diag of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/DensityPointOfCornerSimple.lean#L169-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/DensityPointOfCornerSimple.lean#L169-L183

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

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.blockDiag_of_mem (x : X) {m : ℕ} (c : d → Fin m) (P : Matrix d d (FractionRing O))
    (h : ∀ g i j, c i ≠ c j → (P * (r g x).map (algebraMap O (FractionRing O)) * P⁻¹) i j = 0)
    (a : X → Matrix d d O) (ha : a ∈ tSpan T r) :
    ∀ i j, c i ≠ c j → (P * (a x).map (algebraMap O (FractionRing O)) * P⁻¹) i j = 0 := by sorry
