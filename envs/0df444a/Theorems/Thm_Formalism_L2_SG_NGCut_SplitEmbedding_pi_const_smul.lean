-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_pi_const_smul
-- name    : Formalism.L2.SG.NGCut.SplitEmbedding.pi_const_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:53:43.469801+00:00
-- url     : https://prove2.me/theorems/d89dc600-f90f-44ea-9309-dfc10278778f
-- title:
--   Split Embedding: pi const smul
-- statement:
--   The Split Embedding construction uses the pi const smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/EmbSInjective.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/EmbSInjective.lean#L13-L21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_BoxFundT
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SwapMp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MeasurablePhiInv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_EmbSInjective
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

theorem Formalism.L2.SG.NGCut.SplitEmbedding.pi_const_smul {ι : Type} [Fintype ι] (x : ℝ) :
    Measure.pi (fun _ : ι => ENNReal.ofReal x • (volume : Measure ℂ)) =
      ENNReal.ofReal x ^ Fintype.card ι • (volume : Measure (ι → ℂ)) := by sorry
