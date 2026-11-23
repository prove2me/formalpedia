-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_cyclotomic_dvd_prod_X_pow_sub_one_sub
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.cyclotomic_dvd_prod_X_pow_sub_one_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:39.236869+00:00
-- url     : https://prove2.me/theorems/c17dd433-98a2-4174-ae0e-89f6d92129e3
-- title:
--   Height Descent Minors: cyclotomic dvd prod X pow sub one sub
-- statement:
--   The Height Descent Minors construction uses the cyclotomic dvd prod X pow sub one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L567-L589
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L567-L589

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.cyclotomic_dvd_prod_X_pow_sub_one_sub (hl2 : l ≠ 2) :
    Polynomial.cyclotomic l ℤ ∣
      (∏ c ∈ Finset.Ioo 0 l, ((Polynomial.X : Polynomial ℤ) ^ c - 1)) - Polynomial.C (l : ℤ) := by sorry
