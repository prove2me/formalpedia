-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylModuleDominanceOfSpan
-- name    : Formalism.GradedWeylDivisibility.dualWeylModuleDominanceOfSpan
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:35:46.681738+00:00
-- url     : https://prove2.me/theorems/a08b7d8b-6d12-4d0b-84a4-91b7ab85c4ab
-- title:
--   Graded Weyl Divisibility: dual Weyl Module Dominance Of Span
-- statement:
--   The Graded Weyl Divisibility construction uses the dual Weyl Module Dominance Of Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylDominanceOf.lean#L41-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylDominanceOf.lean#L41-L81

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantDominance
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
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

theorem Formalism.GradedWeylDivisibility.dualWeylModuleDominanceOfSpan : DualWeylDominanceOf := by sorry
