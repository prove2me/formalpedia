-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_det_submatrix_mul_right
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.dvd_det_submatrix_mul_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:28:36.750192+00:00
-- url     : https://prove2.me/theorems/db68c184-bca5-47bf-a08e-26208545680b
-- title:
--   Height Descent Minors: dvd det submatrix mul right
-- statement:
--   The Height Descent Minors construction uses the dvd det submatrix mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1450-L1457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1450-L1457

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.dvd_det_submatrix_mul_right {α β γ τ : Type} [Fintype β] [Fintype τ] [DecidableEq τ] (x : R)
    (P : Matrix α β R) (H : Matrix β γ R)
    (h : ∀ (f : τ → α) (g : τ → β), x ∣ (P.submatrix f g).det) (f : τ → α) (g : τ → γ) :
    x ∣ ((P * H).submatrix f g).det := by sorry
