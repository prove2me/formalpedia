-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_swap_mp
-- name    : Formalism.L2.SG.NGCut.SplitEmbedding.swap_mp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:47:14.319026+00:00
-- url     : https://prove2.me/theorems/b31747f6-394c-4b44-8861-46d0218c4934
-- title:
--   Split Embedding: swap mp
-- statement:
--   The Split Embedding construction uses the swap mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/SwapMp.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/SwapMp.lean#L10-L13

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdBisForm_Imports
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SwapMp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasurableSpace Set
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding

theorem Formalism.L2.SG.NGCut.SplitEmbedding.swap_mp {ι P β : Type} [Fintype ι] [Fintype P] [MeasurableSpace β] (μ0 : Measure β) [SigmaFinite μ0] :
    MeasurePreserving (fun (x : ι → P → β) (p : P) (v : ι) => x v p)
      (Measure.pi fun _ : ι => Measure.pi fun _ : P => μ0) (Measure.pi fun _ : P => Measure.pi fun _ : ι => μ0) := by sorry
