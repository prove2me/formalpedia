-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_q_dvd_binomialSeriesSubOne_sub_pow
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.q_dvd_binomialSeriesSubOne_sub_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:33.745534+00:00
-- url     : https://prove2.me/theorems/1ce980c9-6142-458d-991a-962d2c8401ce
-- title:
--   Height Descent Minors: q dvd binomial Series Sub One sub pow
-- statement:
--   The Height Descent Minors construction uses the q dvd binomial Series Sub One sub pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L608-L623
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L608-L623

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.q_dvd_binomialSeriesSubOne_sub_pow (ha : ActLaws) (hq : QMul) (c : ℕ) (e : ℤ_[l]) :
    q l ℤ_[l] ∣ br l ℤ_[l] ((c : ℤ_[l]) + (l : ℤ_[l]) * e) - ((1 + X) ^ c - 1) := by sorry
