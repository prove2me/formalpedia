-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_averagedSeries_subst_invariant
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.averagedSeries_subst_invariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:24.594283+00:00
-- url     : https://prove2.me/theorems/547fe8ba-40c0-447c-ba20-c1cebf6907be
-- title:
--   Height Descent Minors: averaged Series subst invariant
-- statement:
--   The Height Descent Minors construction uses the averaged Series subst invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L938-L961
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L938-L961

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.averagedSeries_subst_invariant (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) (s f : R⟦X⟧)
    (hP : ((w : R⟦X⟧) * X ^ n).subst (X * s) = (w : R⟦X⟧) * X ^ n)
    (hinv : f.subst (X * s) = f)
    (hu : ∀ j, 0 < j → j < n → IsUnit (constantCoeff s ^ j - 1)) :
    (divQuotient n w f).subst (X * s) = divQuotient n w f := by sorry
