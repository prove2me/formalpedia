-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_weylRational
-- name    : Formalism.GradedWeylDivisibility.weylRational
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:59:45.473957+00:00
-- url     : https://prove2.me/theorems/080bdf30-51af-4052-9389-d53df34e7066
-- title:
--   Graded Weyl Divisibility: weyl Rational
-- statement:
--   The Graded Weyl Divisibility construction uses the weyl Rational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FinalB.lean#L26-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FinalB.lean#L26-L26

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

theorem Formalism.GradedWeylDivisibility.weylRational : WeylRational := by sorry
