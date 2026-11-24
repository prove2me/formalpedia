-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_prod
-- name    : Formalism.CohomologicalDescent.LD.ld_prod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:40:37.398481+00:00
-- url     : https://prove2.me/theorems/e7de2c3a-14b6-4da9-994a-6d1ade8145f2
-- title:
--   LD: ld prod
-- statement:
--   The LD construction uses the ld prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L386-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L386-L408

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

theorem Formalism.CohomologicalDescent.LD.ld_prod {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ 2) (I : ∀ k, Fin (sz k) → Fin 2)
    (S : Finset (Fin K)) :
    ∃ (ε : ℤ) (α β : ℕ), ∏ k ∈ S, initMinor ℤ (I k) (hsz k) =
        C ε * (X (0, 0) ^ α * X (1, 0) ^ β * ldDet ^ (S.filter fun k => 1 < sz k).card) ∧
      α + β + (S.filter fun k => 1 < sz k).card = (S.filter fun k => 0 < sz k).card := by sorry
