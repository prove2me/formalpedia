-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_closedEqNabla
-- name    : Formalism.GradedWeylDivisibility.closedEqNabla
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:14.51225+00:00
-- url     : https://prove2.me/theorems/81209668-252c-409d-947c-9a835aafcd53
-- title:
--   Graded Weyl Divisibility: closed Eq Nabla
-- statement:
--   The Graded Weyl Divisibility construction uses the closed Eq Nabla property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FinalB.lean#L23-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FinalB.lean#L23-L23

import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLine
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLineTall
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQPos
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQBilin
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivClosedGraded
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWInClosed
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaTallZero
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylEqNablaQ
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylRationalOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.closedEqNabla : ClosedEqNabla := by sorry
