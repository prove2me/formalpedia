-- Prove2me | Theorems.Thm_Formalism_F_det_gram_eq_normDet_sq
-- name    : Formalism.F.det_gram_eq_normDet_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:31.225104+00:00
-- url     : https://prove2.me/theorems/ab001d06-2cd5-4f83-b4ca-fdfa97cd64ae
-- title:
--   F: det gram eq norm Det sq
-- statement:
--   The F construction uses the det gram eq norm Det sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/GramDetLe.lean#L81-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/GramDetLe.lean#L81-L124

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

theorem Formalism.F.det_gram_eq_normDet_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) :
    (Matrix.gram ℝ v).det = (linearCombinationMap v).normDet ^ 2 := by sorry
