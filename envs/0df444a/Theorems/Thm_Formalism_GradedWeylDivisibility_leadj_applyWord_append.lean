-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_leadj_applyWord_append
-- name    : Formalism.GradedWeylDivisibility.leadj_applyWord_append
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:13.6752+00:00
-- url     : https://prove2.me/theorems/002c6dac-f8d9-4fc9-bbc2-db74eacb4f52
-- title:
--   Graded Weyl Divisibility: leadj apply Word append
-- statement:
--   The Graded Weyl Divisibility construction uses the leadj apply Word append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQWordAdj.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQWordAdj.lean#L12-L16

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

theorem Formalism.GradedWeylDivisibility.leadj_applyWord_append {r n : ℕ} (l1 l2 : List (Fin r × Fin r × ℕ))
    (F : MvPolynomial (Fin r × Fin n) ℚ) :
    applyWord ℚ (l1 ++ l2) F = applyWord ℚ l1 (applyWord ℚ l2 F) := by sorry
