-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_step_apply
-- name    : Formalism.GradedWeylDivisibility.lhwline_step_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:33.238873+00:00
-- url     : https://prove2.me/theorems/973a5cfe-9074-4079-9c19-1fdb0d2d19bf
-- title:
--   Graded Weyl Divisibility: lhwline step apply
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwline step apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L177-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L177-L184

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

theorem Formalism.GradedWeylDivisibility.lhwline_step_apply (p : Fin r) (q : Fin n) (x : Fin r × Fin n → K) (a : Fin r) (j : Fin n) :
    highestWeightLineUpdate p q x (a, j) =
      (if p < a then x (a, j) + -(x (a, q) / x (p, q)) * x (p, j) else x (a, j)) +
      (if q < j then -(x (p, j) / x (p, q)) *
        (if p < a then x (a, q) + -(x (a, q) / x (p, q)) * x (p, q) else x (a, q)) else 0) := by sorry
