-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_leadj_transposeWord_cons
-- name    : Formalism.GradedWeylDivisibility.leadj_transposeWord_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:13.601391+00:00
-- url     : https://prove2.me/theorems/c04ff500-cae1-4c8c-8c76-3f0ccdfa1b1f
-- title:
--   Graded Weyl Divisibility: leadj transpose Word cons
-- statement:
--   The Graded Weyl Divisibility construction uses the leadj transpose Word cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQWordAdj.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQWordAdj.lean#L18-L20

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

theorem Formalism.GradedWeylDivisibility.leadj_transposeWord_cons {r : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ)) :
    transposeWord (x :: w) = transposeWord w ++ [(x.2.1, x.1, x.2.2)] := by sorry
