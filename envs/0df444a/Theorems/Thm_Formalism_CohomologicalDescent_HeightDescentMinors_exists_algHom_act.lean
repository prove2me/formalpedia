-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_algHom_act
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.exists_algHom_act
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:28:53.433363+00:00
-- url     : https://prove2.me/theorems/21eaddb8-5130-4570-a158-db69e891810c
-- title:
--   Height Descent Minors: exists alg Hom act
-- statement:
--   The Height Descent Minors construction uses the exists alg Hom act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1172-L1175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1172-L1175

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.exists_algHom_act (c : ℤ_[l]) :
    ∃ Φ : O⟦X⟧ →ₐ[O] O⟦X⟧, ∀ f, act l O c f = Φ f := by sorry
