-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_point_pi
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.point_pi
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:32:26.561799+00:00
-- url     : https://prove2.me/theorems/329c3a06-11b2-453a-a65c-0dc0c6ee31be
-- title:
--   ring Data Objects: point pi
-- statement:
--   The ring Data Objects construction uses the point pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/DensityPointOfCornerSimple.lean#L255-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/DensityPointOfCornerSimple.lean#L255-L322

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

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.point_pi {O : Type} [CommRing O] [IsDomain O] {X : Type} (T : Subalgebra O (X → O)) {d : Type}
    [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O)) (π : X) {t : ℕ}
    (bl : d → Fin (t + 1)) (χ₁ ε : G →* Oˣ) (hP : PrimHyp O T r π bl χ₁ ε) (eB : X → Matrix d d O)
    (heBπ : eB π = Matrix.diagonal (fun a => if bl a = 0 then 0 else 1)) (g₀ : G)
    (hε : ∀ i j : ℕ, i < t → j < t → (ε g₀) ^ i = (ε g₀) ^ j → i = j) :
    (blockPoly ((eB π).map (algebraMap O (FractionRing O)))
      ((eB π * r g₀ π * eB π).map (algebraMap O (FractionRing O)))).Separable := by sorry
