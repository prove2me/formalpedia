-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_fischerInnerWeightOrthogonal_holds
-- name    : Formalism.GradedWeylDivisibility.fischerInnerWeightOrthogonal_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:29.342813+00:00
-- url     : https://prove2.me/theorems/3e3a6766-05a9-4206-817d-38a810682db4
-- title:
--   Graded Weyl Divisibility: fischer Inner Weight Orthogonal holds
-- statement:
--   The Graded Weyl Divisibility construction uses the fischer Inner Weight Orthogonal holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockWeightOrth.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockWeightOrth.lean#L9-L16

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockWeightOrth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.fischerInnerWeightOrthogonal_holds : FockWeightOrth := by sorry
