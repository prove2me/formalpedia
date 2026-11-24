-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_hwInClosed
-- name    : Formalism.GradedWeylDivisibility.hwInClosed
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:06.618818+00:00
-- url     : https://prove2.me/theorems/1bb1cd61-7e6c-4b6c-8cab-07c0c60aa2a7
-- title:
--   Graded Weyl Divisibility: hw In Closed
-- statement:
--   The Graded Weyl Divisibility construction uses the hw In Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FinalB.lean#L22-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FinalB.lean#L22-L22

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

theorem Formalism.GradedWeylDivisibility.hwInClosed : HWInClosed := by sorry
