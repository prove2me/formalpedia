-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_pow_prime_eq_subst_X_pow
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.pow_prime_eq_subst_X_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:20.209926+00:00
-- url     : https://prove2.me/theorems/1dd79073-be85-47f5-a91f-06cc7528b032
-- title:
--   Height Descent Minors: pow prime eq subst X pow
-- statement:
--   The Height Descent Minors construction uses the pow prime eq subst X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L501-L507
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L501-L507

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
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.pow_prime_eq_subst_X_pow (F : (ZMod l)⟦X⟧) : F ^ l = F.subst (X ^ l : (ZMod l)⟦X⟧) := by sorry
