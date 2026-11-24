-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_divided_power_cofactor
-- name    : Formalism.CohomologicalDescent.LD.divided_power_cofactor
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:06:01.69642+00:00
-- url     : https://prove2.me/theorems/22d15469-8104-473f-b145-21d68d63878a
-- title:
--   LD: divided power cofactor
-- statement:
--   The LD construction uses the divided power cofactor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L833-L837
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L833-L837

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

theorem Formalism.CohomologicalDescent.LD.divided_power_cofactor {r : ℕ} (a b : Fin r) (hab : a ≠ b) (k : ℕ) (x : MvPolynomial (Fin r × Fin r) ℤ) :
    rowDiv ℤ a b k (cofMap r x) = (-1) ^ k * cofMap r (rowDiv ℤ (Fin.rev b) (Fin.rev a) k x) := by sorry
