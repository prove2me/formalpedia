-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_det_submatrix_eq_or_neg
-- name    : Formalism.CohomologicalDescent.LD.det_submatrix_eq_or_neg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:06:08.452639+00:00
-- url     : https://prove2.me/theorems/dd13b482-c6ca-426a-8b80-981cffac4a04
-- title:
--   LD: det submatrix eq or neg
-- statement:
--   The LD construction uses the det submatrix eq or neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L305-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L305-L312

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
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
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA

theorem Formalism.CohomologicalDescent.LD.det_submatrix_eq_or_neg {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (A : Matrix m m R) (ρ γ : n ≃ m) :
    (A.submatrix ρ γ).det = A.det ∨ (A.submatrix ρ γ).det = -A.det := by sorry
