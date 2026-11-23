-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_q_dvd_prod_sub_l
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.q_dvd_prod_sub_l
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:25.322954+00:00
-- url     : https://prove2.me/theorems/b0b6daee-4385-4502-a4da-06a72b346c94
-- title:
--   Height Descent Minors: q dvd prod sub l
-- statement:
--   The Height Descent Minors construction uses the q dvd prod sub l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L591-L606
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L591-L606

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.q_dvd_prod_sub_l (hq : QMul) (hl2 : l ≠ 2) :
    q l ℤ_[l] ∣ (∏ c ∈ Finset.Ioo 0 l, ((1 + X : ℤ_[l]⟦X⟧) ^ c - 1)) - C (l : ℤ_[l]) := by sorry
