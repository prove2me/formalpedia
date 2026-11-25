-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_phiInv_phiMap
-- name    : Formalism.L2.SG.NGCut.SplitEmbedding.phiInv_phiMap
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:21.303677+00:00
-- url     : https://prove2.me/theorems/4b6d1731-2ff9-416b-8a8c-4730e272ae70
-- title:
--   Split Embedding: phi Inv phi Map
-- statement:
--   The Split Embedding construction uses the phi Inv phi Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MeasurablePhiInv.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MeasurablePhiInv.lean#L23-L25

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CosetFd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MeasurablePhiInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding
variable {K : Type} [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}] {ι : Type} [Fintype ι]
  (σ : ι ≃ {w : InfinitePlace K // w.IsComplex}) (cj : ι → Prop) [DecidablePred cj]

theorem Formalism.L2.SG.NGCut.SplitEmbedding.phiInv_phiMap (x : mixedSpace K) : phiInv σ cj (phiMap σ cj x) = x := by sorry
