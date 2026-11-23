-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_q_dvd_q_zero_of_ne_two
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.q_dvd_q_zero_of_ne_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:28.274376+00:00
-- url     : https://prove2.me/theorems/61d52c94-0186-406d-84ce-3483af5c35c3
-- title:
--   Height Descent Minors: q dvd q zero of ne two
-- statement:
--   The Height Descent Minors construction uses the q dvd q zero of ne two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L659-L676
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L659-L676

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable (l : ℕ) [Fact l.Prime]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.q_dvd_q_zero_of_ne_two (ha : ActLaws) (hm : MuFacts) (hq : QMul) (hl2 : l ≠ 2) :
    q l ℤ_[l] ∣ q0 l ℤ_[l] := by sorry
