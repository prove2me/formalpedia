-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_fischerInnerRatBilinear
-- name    : Formalism.GradedWeylDivisibility.fischerInnerRatBilinear
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:35.361957+00:00
-- url     : https://prove2.me/theorems/cf9a017c-27da-471a-8626-b0f04b98a612
-- title:
--   Graded Weyl Divisibility: fischer Inner Rat Bilinear
-- statement:
--   The Graded Weyl Divisibility construction uses the fischer Inner Rat Bilinear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQBilin.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQBilin.lean#L10-L11

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQBilin
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

theorem Formalism.GradedWeylDivisibility.fischerInnerRatBilinear : FockQBilin := by sorry
