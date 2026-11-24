-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_highestWeightVectorNeZero
-- name    : Formalism.GradedWeylDivisibility.highestWeightVectorNeZero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:39.803096+00:00
-- url     : https://prove2.me/theorems/f93f19a4-4298-43ad-a31c-ab787ee3bf67
-- title:
--   Graded Weyl Divisibility: highest Weight Vector Ne Zero
-- statement:
--   The Graded Weyl Divisibility construction uses the highest Weight Vector Ne Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/HighestWeightVectorNeZero.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/HighestWeightVectorNeZero.lean#L8-L20

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HighestWeightVectorNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GradedWeylDivisibility
open MvPolynomial

theorem Formalism.GradedWeylDivisibility.highestWeightVectorNeZero : HWNe := by sorry
