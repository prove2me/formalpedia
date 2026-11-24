-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_divided_power_det_pow_mul
-- name    : Formalism.CohomologicalDescent.LD.divided_power_det_pow_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:05:55.476094+00:00
-- url     : https://prove2.me/theorems/82077dc5-e395-49c4-8183-4ee050956180
-- title:
--   LD: divided power det pow mul
-- statement:
--   The LD construction uses the divided power det pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L839-L843
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L839-L843

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

theorem Formalism.CohomologicalDescent.LD.divided_power_det_pow_mul {r : ℕ} (a b : Fin r) (hab : a ≠ b) (k n : ℕ) (f : MvPolynomial (Fin r × Fin r) ℤ) :
    rowDiv ℤ a b k (genericDet ℤ r ^ n * f) = genericDet ℤ r ^ n * rowDiv ℤ a b k f := by sorry
