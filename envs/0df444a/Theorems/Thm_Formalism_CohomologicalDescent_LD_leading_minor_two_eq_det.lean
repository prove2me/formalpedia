-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_leading_minor_two_eq_det
-- name    : Formalism.CohomologicalDescent.LD.leading_minor_two_eq_det
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:21.975156+00:00
-- url     : https://prove2.me/theorems/efd629e7-ce71-4c5b-8e52-ba6cbdfa1641
-- title:
--   LD: leading minor two eq det
-- statement:
--   The LD construction uses the leading minor two eq det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L211-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L211-L214

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility

theorem Formalism.CohomologicalDescent.LD.leading_minor_two_eq_det (h1 : 2 ≤ 2) (h2 : 2 ≤ 2) : lpMinor ℤ (r := 2) (n := 2) 2 h1 h2 = ldDet := by sorry
