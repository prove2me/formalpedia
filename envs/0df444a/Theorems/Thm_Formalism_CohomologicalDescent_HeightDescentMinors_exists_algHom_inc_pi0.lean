-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_algHom_inc_pi0
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.exists_algHom_inc_pi0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:39.646465+00:00
-- url     : https://prove2.me/theorems/1539ab88-8c1b-4ab7-9a30-beb581d14ecc
-- title:
--   Height Descent Minors: exists alg Hom inc pi0
-- statement:
--   The Height Descent Minors construction uses the exists alg Hom inc pi0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1166-L1170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1166-L1170

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.exists_algHom_inc_pi0 (hm : MuFacts) :
    ∃ Φ : O⟦X⟧ →ₐ[O] O⟦X⟧, (∀ f, inc l O f = Φ f) ∧ Φ X = pi0 l O := by sorry
