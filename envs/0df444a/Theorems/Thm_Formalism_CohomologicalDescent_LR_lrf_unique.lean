-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_unique
-- name    : Formalism.CohomologicalDescent.LR.lrf_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:54.999891+00:00
-- url     : https://prove2.me/theorems/09426114-ccdb-4577-8c84-31724a2a1f09
-- title:
--   LR: lrf unique
-- statement:
--   The LR construction uses the lrf unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L458-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L458-L479

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}

theorem Formalism.CohomologicalDescent.LR.lrf_unique (m e : Fin r × Fin n →₀ ℕ) (hm : LowerTri m) (he : LowerTri e) (hoff : lrf_off m = lrf_off e)
    (hcol : ∀ s : Fin n, ∑ a : Fin r, m (a, s) = ∑ a : Fin r, e (a, s)) : m = e := by sorry
