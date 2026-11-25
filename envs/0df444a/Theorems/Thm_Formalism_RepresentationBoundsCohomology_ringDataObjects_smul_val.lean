-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_smul_val
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.smul_val
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:53:22.960218+00:00
-- url     : https://prove2.me/theorems/375f5738-6a2e-4471-ac4a-7dd5aa99455d
-- title:
--   ring Data Objects: smul val
-- statement:
--   The ring Data Objects construction uses the smul val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/FinrankRangeEq.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/FinrankRangeEq.lean#L61-L66

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_RankDiagIte
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_BridgeDet
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq
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
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type}
  (T' : Subalgebra O (X' → O)) {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Group G]
  (rK : G →* (X' → Matrix d d (FractionRing O)))

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.smul_val (f : T') (a : spanSub T' rK) (y : X') :
    (letI := algRp T' rK; (f • a : spanSub T' rK)).1 y =
      algebraMap O (FractionRing O) (f.1 y) • a.1 y := by sorry
