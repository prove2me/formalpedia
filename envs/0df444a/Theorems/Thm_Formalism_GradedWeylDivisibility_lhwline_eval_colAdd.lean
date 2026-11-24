-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_eval_colAdd
-- name    : Formalism.GradedWeylDivisibility.lhwline_eval_colAdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:32.049891+00:00
-- url     : https://prove2.me/theorems/ab604495-c228-46bd-a095-838d21822e34
-- title:
--   Graded Weyl Divisibility: lhwline eval col Add
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwline eval col Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L37-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L37-L48

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
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
variable {K : Type*} [Field K] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.lhwline_eval_colAdd (l j : Fin n) (c : K) (x : Fin r × Fin n → K)
    (g : MvPolynomial (Fin r × Fin n) K) :
    eval x (colAdd K l j c g) = eval (lhwline_colOp l j c x) g := by sorry
