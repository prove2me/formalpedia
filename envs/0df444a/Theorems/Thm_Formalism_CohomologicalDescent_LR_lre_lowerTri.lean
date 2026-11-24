-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lre_lowerTri
-- name    : Formalism.CohomologicalDescent.LR.lre_lowerTri
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:08.765029+00:00
-- url     : https://prove2.me/theorems/3d16d69c-67d3-42aa-ad2b-0f89d8905734
-- title:
--   LR: lre lower Tri
-- statement:
--   The LR construction uses the lre lower Tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LowerTriangularIntegral.lean#L27-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LowerTriangularIntegral.lean#L27-L42

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

theorem Formalism.CohomologicalDescent.LR.lre_lowerTri {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r)
    (hI : ∀ k, StrictMono (I k)) : LowerTri (bidetExp sz hsz I) := by sorry
