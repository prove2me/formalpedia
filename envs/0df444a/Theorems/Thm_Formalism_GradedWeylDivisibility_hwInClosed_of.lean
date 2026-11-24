-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_hwInClosed_of
-- name    : Formalism.GradedWeylDivisibility.hwInClosed_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:44.323107+00:00
-- url     : https://prove2.me/theorems/96f1d168-dcc2-4a2a-8f8f-077f68072a38
-- title:
--   Graded Weyl Divisibility: hw In Closed of
-- statement:
--   The Graded Weyl Divisibility construction uses the hw In Closed of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/HWInClosed.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/HWInClosed.lean#L10-L20

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWInClosed
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

theorem Formalism.GradedWeylDivisibility.hwInClosed_of (h1 : HWLine) (h2 : RowDivClosedGraded) : HWInClosed := by sorry
