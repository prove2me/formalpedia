-- Prove2me | Theorems.Thm_Formalism_F_linearCombinationMap_apply
-- name    : Formalism.F.linearCombinationMap_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:21:56.965256+00:00
-- url     : https://prove2.me/theorems/08ffda8c-f408-460a-808b-b66346754f3b
-- title:
--   F: linear Combination Map apply
-- statement:
--   The F construction uses the linear Combination Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/GramDetLe.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/GramDetLe.lean#L50-L52

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.F

theorem Formalism.F.linearCombinationMap_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (v : ι → E) (c : EuclideanSpace ℝ ι) :
    linearCombinationMap v c = ∑ i, c i • v i := by sorry
