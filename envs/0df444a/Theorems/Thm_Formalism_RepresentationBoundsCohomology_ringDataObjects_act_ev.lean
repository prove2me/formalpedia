-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_act_ev
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.act_ev
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:54:22.006317+00:00
-- url     : https://prove2.me/theorems/130deb63-f3b1-54a4-ab6e-9000954c625a
-- title:
--   ring Data Objects: act ev
-- statement:
--   The ring Data Objects construction uses the act ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/FinrankRangeEq.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/FinrankRangeEq.lean#L68-L69

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

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.act_ev (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) (x' : X') (a : R')
    (v : EvalSp O d R' x') : a • v = fun i => ∑ j, a.1 x' i j • (v j : FractionRing O) := by sorry
