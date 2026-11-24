-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_highestWeightVectorRaising
-- name    : Formalism.GradedWeylDivisibility.highestWeightVectorRaising
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:36.782119+00:00
-- url     : https://prove2.me/theorems/8d00df92-7904-4ce3-b384-23c9fc23cd01
-- title:
--   Graded Weyl Divisibility: highest Weight Vector Raising
-- statement:
--   The Graded Weyl Divisibility construction uses the highest Weight Vector Raising property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/HWRaise.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/HWRaise.lean#L67-L70

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRaise
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

theorem Formalism.GradedWeylDivisibility.highestWeightVectorRaising : HWRaise := by sorry
