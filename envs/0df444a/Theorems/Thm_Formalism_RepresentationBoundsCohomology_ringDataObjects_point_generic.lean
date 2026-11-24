-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_point_generic
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.point_generic
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:29:13.249056+00:00
-- url     : https://prove2.me/theorems/570776da-5ede-42da-ba2f-236a2664f778
-- title:
--   ring Data Objects: point generic
-- statement:
--   The ring Data Objects construction uses the point generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/DensityPointOfCornerSimple.lean#L187-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/DensityPointOfCornerSimple.lean#L187-L253

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

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.point_generic (hD : StatDensity) (hC : StatCornerSimple) {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {X : Type} [Fintype X] (T : Subalgebra O (X → O)) {d : Type} [Fintype d]
    [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (eB : X → Matrix d d O) (heBm : eB ∈ tSpan T r)
    (heBB : eB * eB = eB) (x : X) (m : ℕ) (c : d → Fin m) (P : Matrix d d (FractionRing O))
    (hG : BlockDiagonalIrreducibleAt (fun g => (r g x).map (algebraMap O (FractionRing O))) m c P) (S0 : Matrix d d O) (w : O)
    (hw : w ≠ 0) :
    ∃ (j : X → O) (a : X → Matrix d d O), j ∈ T ∧ (∀ y, y ≠ x → j y = 0) ∧ a ∈ tSpan T r ∧
      (blockPoly ((eB x).map (algebraMap O (FractionRing O)))
        ((eB x * S0 * eB x + w • (j x • (eB x * a x * eB x))).map
          (algebraMap O (FractionRing O)))).Separable := by sorry
