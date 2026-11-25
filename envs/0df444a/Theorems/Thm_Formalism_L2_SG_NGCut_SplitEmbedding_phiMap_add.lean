-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_phiMap_add
-- name    : Formalism.L2.SG.NGCut.SplitEmbedding.phiMap_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:15:56.800089+00:00
-- url     : https://prove2.me/theorems/5cb0fc78-7fe0-4dee-9ce1-49a66844f8f4
-- title:
--   Split Embedding: phi Map add
-- statement:
--   The Split Embedding construction uses the phi Map add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/PhiMapAdd.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/PhiMapAdd.lean#L18-L20

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

theorem Formalism.L2.SG.NGCut.SplitEmbedding.phiMap_add (x y : mixedSpace K) : phiMap σ cj (x + y) = phiMap σ cj x + phiMap σ cj y := by sorry
