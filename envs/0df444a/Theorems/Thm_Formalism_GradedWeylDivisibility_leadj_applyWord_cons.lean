-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_leadj_applyWord_cons
-- name    : Formalism.GradedWeylDivisibility.leadj_applyWord_cons
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:11.323524+00:00
-- url     : https://prove2.me/theorems/c3bec6cb-5dbc-4faf-87e1-6acf2e601253
-- title:
--   Graded Weyl Divisibility: leadj apply Word cons
-- statement:
--   The Graded Weyl Divisibility construction uses the leadj apply Word cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQWordAdj.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQWordAdj.lean#L7-L10

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.leadj_applyWord_cons {r n : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ))
    (F : MvPolynomial (Fin r × Fin n) ℚ) :
    applyWord ℚ (x :: w) F = rowDiv ℚ x.1 x.2.1 x.2.2 (applyWord ℚ w F) := by sorry
