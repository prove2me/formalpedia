-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_highestWeightCount_self_eq_succ_of_lt
-- name    : Formalism.GradedWeylDivisibility.highestWeightCount_self_eq_succ_of_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:27.924689+00:00
-- url     : https://prove2.me/theorems/460d94b6-bec1-428f-99a1-57584947aab5
-- title:
--   Graded Weyl Divisibility: highest Weight Count self eq succ of lt
-- statement:
--   The Graded Weyl Divisibility construction uses the highest Weight Count self eq succ of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L171-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L171-L174

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
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

theorem Formalism.GradedWeylDivisibility.highestWeightCount_self_eq_succ_of_lt {r n : ℕ} {a b : Fin r} (hab : a < b) (s : Fin n) :
    lehwP (n := n) a (a, s) = lehwP a (b, s) + 1 := by sorry
