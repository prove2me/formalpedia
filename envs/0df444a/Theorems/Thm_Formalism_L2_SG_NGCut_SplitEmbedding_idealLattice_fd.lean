-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_idealLattice_fd
-- name    : Formalism.L2.SG.NGCut.SplitEmbedding.idealLattice_fd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:15:35.386422+00:00
-- url     : https://prove2.me/theorems/7fd9b124-2314-5413-b42b-f32d8cd5363f
-- title:
--   Split Embedding: ideal Lattice fd
-- statement:
--   The Split Embedding construction uses the ideal Lattice fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MeasurablePhiInv.lean#L50-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MeasurablePhiInv.lean#L50-L64

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

theorem Formalism.L2.SG.NGCut.SplitEmbedding.idealLattice_fd (K : Type) [Field K] [NumberField K] (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
    ∃ FL : Set (mixedSpace K), MeasurableSet FL ∧
      (∀ x, ∃! l : (idealLattice K I).toAddSubgroup, (l : mixedSpace K) + x ∈ FL) := by sorry
