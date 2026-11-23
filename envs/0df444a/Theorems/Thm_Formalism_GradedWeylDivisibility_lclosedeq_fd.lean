-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_fd
-- name    : Formalism.GradedWeylDivisibility.lclosedeq_fd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:24.701798+00:00
-- url     : https://prove2.me/theorems/9f3553de-329e-44d2-a61e-5b4d70133763
-- title:
--   Graded Weyl Divisibility: lclosedeq fd
-- statement:
--   The Graded Weyl Divisibility construction uses the lclosedeq fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/ClosedEqNabla.lean#L19-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/ClosedEqNabla.lean#L19-L46

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

theorem Formalism.GradedWeylDivisibility.lclosedeq_fd (r n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℚ (dualWeyl ℚ r n ν) := by sorry
