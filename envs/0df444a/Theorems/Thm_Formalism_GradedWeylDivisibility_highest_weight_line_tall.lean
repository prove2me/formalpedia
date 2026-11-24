-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_highest_weight_line_tall
-- name    : Formalism.GradedWeylDivisibility.highest_weight_line_tall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:52.737802+00:00
-- url     : https://prove2.me/theorems/48a053d3-2171-4132-aa3f-a1472b5834ff
-- title:
--   Graded Weyl Divisibility: highest weight line tall
-- statement:
--   The Graded Weyl Divisibility construction uses the highest weight line tall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/HWLineTall.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/HWLineTall.lean#L11-L16

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLineTall
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

theorem Formalism.GradedWeylDivisibility.highest_weight_line_tall : HWLineTall := by sorry
