-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_coeff_ell
-- name    : Formalism.CohomologicalDescent.LR.lrf_coeff_ell
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:35.708373+00:00
-- url     : https://prove2.me/theorems/6566da07-1f65-443a-802f-09ac2011d1e3
-- title:
--   LR: lrf coeff ell
-- statement:
--   The LR construction uses the lrf coeff ell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L481-L508
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L481-L508

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

theorem Formalism.CohomologicalDescent.LR.lrf_coeff_ell (ν : Fin n → ℕ) (F : MvPolynomial (Fin r × Fin n) R) (e : Fin r × Fin n →₀ ℕ)
    (hF : IsWeightedHomogeneous (colW r n) F ν) (he : LowerTri e) (hcol : ∀ s : Fin n, ∑ a : Fin r, e (a, s) = ν s) :
    coeff (lrf_off e) (eval₂ C (lrf_ell R r n) F) = coeff e F := by sorry
