-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_det_submatrix_mul_left
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.dvd_det_submatrix_mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:53.136257+00:00
-- url     : https://prove2.me/theorems/68df1ccf-c6d5-4707-ba94-3404fedbd855
-- title:
--   Height Descent Minors: dvd det submatrix mul left
-- statement:
--   The Height Descent Minors construction uses the dvd det submatrix mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1443-L1448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1443-L1448

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.dvd_det_submatrix_mul_left {α β γ τ : Type} [Fintype β] [Fintype τ] [DecidableEq τ] (x : R)
    (G : Matrix α β R) (P : Matrix β γ R)
    (h : ∀ (f : τ → β) (g : τ → γ), x ∣ (P.submatrix f g).det) (f : τ → α) (g : τ → γ) :
    x ∣ ((G * P).submatrix f g).det := by sorry
