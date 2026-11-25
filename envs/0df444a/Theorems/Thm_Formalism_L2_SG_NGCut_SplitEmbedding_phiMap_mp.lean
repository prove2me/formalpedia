-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_phiMap_mp
-- name    : Formalism.L2.SG.NGCut.SplitEmbedding.phiMap_mp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:07.447055+00:00
-- url     : https://prove2.me/theorems/dc3b68b8-0840-57b3-bc43-ba9a32c714e2
-- title:
--   Split Embedding: phi Map mp
-- statement:
--   The Split Embedding construction uses the phi Map mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/PhiMapAdd.lean#L22-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/PhiMapAdd.lean#L22-L59

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MassSplit
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_PhiMapAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open MeasureTheory NumberField NumberField.mixedEmbedding
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (σ : ι ≃ {w : InfinitePlace K // w.IsComplex}) (cj : ι → Prop) [DecidablePred cj]

theorem Formalism.L2.SG.NGCut.SplitEmbedding.phiMap_mp [IsEmpty {w : InfinitePlace K // w.IsReal}] :
    MeasurePreserving (phiMap σ cj) volume volume := by sorry
