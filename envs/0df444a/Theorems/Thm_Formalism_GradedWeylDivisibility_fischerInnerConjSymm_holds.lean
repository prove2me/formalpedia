-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_fischerInnerConjSymm_holds
-- name    : Formalism.GradedWeylDivisibility.fischerInnerConjSymm_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:54:00.943659+00:00
-- url     : https://prove2.me/theorems/7eba0108-30da-4d22-9554-f6898524535e
-- title:
--   Graded Weyl Divisibility: fischer Inner Conj Symm holds
-- statement:
--   The Graded Weyl Divisibility construction uses the fischer Inner Conj Symm holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockHerm.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockHerm.lean#L10-L12

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockHerm
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

theorem Formalism.GradedWeylDivisibility.fischerInnerConjSymm_holds : FockHerm := by sorry
