-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_subst_of_invariant
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.exists_subst_of_invariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:25.772105+00:00
-- url     : https://prove2.me/theorems/65ab6454-d780-4349-97c1-02c55d4f67c0
-- title:
--   Height Descent Minors: exists subst of invariant
-- statement:
--   The Height Descent Minors construction uses the exists subst of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L963-L990
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L963-L990

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
variable {R : Type} [CommRing R]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.exists_subst_of_invariant (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) (s f : R⟦X⟧)
    (hP : ((w : R⟦X⟧) * X ^ n).subst (X * s) = (w : R⟦X⟧) * X ^ n)
    (hinv : f.subst (X * s) = f)
    (hu : ∀ j, 0 < j → j < n → IsUnit (constantCoeff s ^ j - 1)) :
    ∃ g : R⟦X⟧, f = g.subst ((w : R⟦X⟧) * X ^ n) := by sorry
