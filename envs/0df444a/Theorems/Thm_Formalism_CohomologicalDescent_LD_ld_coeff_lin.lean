-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_coeff_lin
-- name    : Formalism.CohomologicalDescent.LD.ld_coeff_lin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:41:43.207219+00:00
-- url     : https://prove2.me/theorems/3c12a038-363b-44a8-b457-8db5a4185b3e
-- title:
--   LD: ld coeff lin
-- statement:
--   The LD construction uses the ld coeff lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L244-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L244-L266

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

theorem Formalism.CohomologicalDescent.LD.ld_coeff_lin {S : Type*} [CommRing S] (a b c : S) (m k : ℕ) :
    ((Polynomial.C a + Polynomial.X * Polynomial.C b) ^ m * Polynomial.C c).coeff k =
      (m.choose k : S) * a ^ (m - k) * b ^ k * c := by sorry
