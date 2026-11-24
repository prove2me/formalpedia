-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_fischerInnerSubstitutionAdjoint
-- name    : Formalism.GradedWeylDivisibility.fischerInnerSubstitutionAdjoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:36.758637+00:00
-- url     : https://prove2.me/theorems/bcd67331-b67a-47e4-81d9-6457967a6a2b
-- title:
--   Graded Weyl Divisibility: fischer Inner Substitution Adjoint
-- statement:
--   The Graded Weyl Divisibility construction uses the fischer Inner Substitution Adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockSubAdj.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockSubAdj.lean#L27-L28

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockSubAdj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.fischerInnerSubstitutionAdjoint : FockSubAdj := by sorry
