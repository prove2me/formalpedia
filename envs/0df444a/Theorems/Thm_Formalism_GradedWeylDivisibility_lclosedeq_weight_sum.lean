-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_weight_sum
-- name    : Formalism.GradedWeylDivisibility.lclosedeq_weight_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:15.47779+00:00
-- url     : https://prove2.me/theorems/2f429482-bbef-4c4b-8c21-c2c7f69a4558
-- title:
--   Graded Weyl Divisibility: lclosedeq weight sum
-- statement:
--   The Graded Weyl Divisibility construction uses the lclosedeq weight sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/ClosedEqNabla.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/ClosedEqNabla.lean#L11-L17

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
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

theorem Formalism.GradedWeylDivisibility.lclosedeq_weight_sum {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) :
    ∑ s : Fin n, Finsupp.weight (colW r n) m s = Finsupp.weight (1 : Fin r × Fin n → ℕ) m := by sorry
