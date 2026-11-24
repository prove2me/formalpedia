-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_weyl_module_rational
-- name    : Formalism.GradedWeylDivisibility.weyl_module_rational
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:10.401832+00:00
-- url     : https://prove2.me/theorems/798bb7d7-caaa-4d8a-9ea1-95996343bbbe
-- title:
--   Graded Weyl Divisibility: weyl module rational
-- statement:
--   The Graded Weyl Divisibility construction uses the weyl module rational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/WeylRationalOf.lean#L112-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/WeylRationalOf.lean#L112-L125

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylRationalOf
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

theorem Formalism.GradedWeylDivisibility.weyl_module_rational : WeylRationalOf := by sorry
