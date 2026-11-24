-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_minor
-- name    : Formalism.CohomologicalDescent.LD.ld_minor
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:41:01.143952+00:00
-- url     : https://prove2.me/theorems/1e65c64c-14cd-4709-872a-d4b80ff717fd
-- title:
--   LD: ld minor
-- statement:
--   The LD construction uses the ld minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L358-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L358-L384

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

theorem Formalism.CohomologicalDescent.LD.ld_minor (s : ℕ) (I : Fin s → Fin 2) (hs : s ≤ 2) :
    (s = 0 ∧ initMinor ℤ I hs = 1) ∨ (s = 1 ∧ ∃ a : Fin 2, initMinor ℤ I hs = X (a, 0)) ∨
      (s = 2 ∧ ∃ ε : ℤ, initMinor ℤ I hs = C ε * ldDet) := by sorry
