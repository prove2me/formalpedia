-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_padicInt_eq_digit_add_mul
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.padicInt_eq_digit_add_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:21.66844+00:00
-- url     : https://prove2.me/theorems/5234506c-4461-466b-a1e9-9d092e69ad77
-- title:
--   Height Descent Minors: padic Int eq digit add mul
-- statement:
--   The Height Descent Minors construction uses the padic Int eq digit add mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L627-L634
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L627-L634

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.padicInt_eq_digit_add_mul (d : ℤ_[l]) :
    ∃ e : ℤ_[l], d = (((PadicInt.toZMod d).val : ℕ) : ℤ_[l]) + (l : ℤ_[l]) * e := by sorry
