-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_det_submatrix_of_minorsDvd
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.dvd_det_submatrix_of_minorsDvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:15.928071+00:00
-- url     : https://prove2.me/theorems/f92ef69f-414d-473a-b3ad-0c6d8b766f24
-- title:
--   Height Descent Minors: dvd det submatrix of minors Dvd
-- statement:
--   The Height Descent Minors construction uses the dvd det submatrix of minors Dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1459-L1484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1459-L1484

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.dvd_det_submatrix_of_minorsDvd {m p t : ℕ} (x : R) (P : Matrix (Fin m) (Fin p) R) (h : MinorsDvd x t P)
    (f : Fin t → Fin m) (g : Fin t → Fin p) : x ∣ (P.submatrix f g).det := by sorry
