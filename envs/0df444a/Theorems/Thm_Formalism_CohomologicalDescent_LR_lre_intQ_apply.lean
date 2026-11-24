-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lre_intQ_apply
-- name    : Formalism.CohomologicalDescent.LR.lre_intQ_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:57.800802+00:00
-- url     : https://prove2.me/theorems/d29b49ff-0733-4217-af76-45ee7ad826b9
-- title:
--   LR: lre int Q apply
-- statement:
--   The LR construction uses the lre int Q apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LowerTriangularIntegral.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LowerTriangularIntegral.lean#L12-L13

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
open scoped MonomialOrder

theorem Formalism.CohomologicalDescent.LR.lre_intQ_apply (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n P = map (Int.castRingHom ℚ) P := by sorry
