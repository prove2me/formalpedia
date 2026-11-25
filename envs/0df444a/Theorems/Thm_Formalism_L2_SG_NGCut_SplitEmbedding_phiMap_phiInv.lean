-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_phiMap_phiInv
-- name    : Formalism.L2.SG.NGCut.SplitEmbedding.phiMap_phiInv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:11.549753+00:00
-- url     : https://prove2.me/theorems/156d84b0-8174-5aca-8ffd-86f3b6c8de21
-- title:
--   Split Embedding: phi Map phi Inv
-- statement:
--   The Split Embedding construction uses the phi Map phi Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MeasurablePhiInv.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MeasurablePhiInv.lean#L19-L21

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

theorem Formalism.L2.SG.NGCut.SplitEmbedding.phiMap_phiInv (v : ι → ℂ) : phiMap σ cj (phiInv σ cj v) = v := by sorry
