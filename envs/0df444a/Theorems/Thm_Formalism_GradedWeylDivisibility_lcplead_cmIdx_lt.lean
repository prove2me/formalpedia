-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lcplead_cmIdx_lt
-- name    : Formalism.GradedWeylDivisibility.lcplead_cmIdx_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:29.428924+00:00
-- url     : https://prove2.me/theorems/3af5cd3e-0e88-427f-858b-39721d1ca9c7
-- title:
--   Graded Weyl Divisibility: lcplead cm Idx lt
-- statement:
--   The Graded Weyl Divisibility construction uses the lcplead cm Idx lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCpleadLemmas.lean#L117-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCpleadLemmas.lean#L117-L131

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

theorem Formalism.GradedWeylDivisibility.lcplead_cmIdx_lt {r n : ℕ} {b a0 : Fin r} {t l : Fin n}
    (h : cmIdx r n (b, t) < cmIdx r n (a0, l)) : t < l ∨ (t = l ∧ b < a0) := by sorry
