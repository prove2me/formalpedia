-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lcplead_cmIdx_val
-- name    : Formalism.GradedWeylDivisibility.lcplead_cmIdx_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:34.356602+00:00
-- url     : https://prove2.me/theorems/e78d391d-52bd-4e42-99b6-ba4f64a6bfd2
-- title:
--   Graded Weyl Divisibility: lcplead cm Idx val
-- statement:
--   The Graded Weyl Divisibility construction uses the lcplead cm Idx val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCpleadLemmas.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCpleadLemmas.lean#L113-L115

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCpleadLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped MonomialOrder
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.lcplead_cmIdx_val {r n : ℕ} (b : Fin r) (t : Fin n) :
    ((cmIdx r n (b, t) : Fin (n * r)) : ℕ) = b + r * t := by sorry
