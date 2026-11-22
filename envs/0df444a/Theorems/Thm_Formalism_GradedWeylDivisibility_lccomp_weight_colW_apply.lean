-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lccomp_weight_colW_apply
-- name    : Formalism.GradedWeylDivisibility.lccomp_weight_colW_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:59:28.196023+00:00
-- url     : https://prove2.me/theorems/2fada20d-b712-43bc-90c6-16db26161e56
-- title:
--   Graded Weyl Divisibility: lccomp weight col W apply
-- statement:
--   The Graded Weyl Divisibility construction uses the lccomp weight col W apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/ColSums.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/ColSums.lean#L9-L15

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
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

theorem Formalism.GradedWeylDivisibility.lccomp_weight_colW_apply {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (t : Fin n) :
    (Finsupp.weight (colW r n) m) t = ∑ a : Fin r, m (a, t) := by sorry
