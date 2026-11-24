-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_semistandardPeel
-- name    : Formalism.GradedWeylDivisibility.semistandardPeel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:18.640557+00:00
-- url     : https://prove2.me/theorems/cde30490-1baf-463b-b3f7-210d3e33e8be
-- title:
--   Graded Weyl Divisibility: semistandard Peel
-- statement:
--   The Graded Weyl Divisibility construction uses the semistandard Peel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/SSYTPeel.lean#L58-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/SSYTPeel.lean#L58-L255

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCssytLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SSYTPeel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.semistandardPeel : SSYTPeel := by sorry
