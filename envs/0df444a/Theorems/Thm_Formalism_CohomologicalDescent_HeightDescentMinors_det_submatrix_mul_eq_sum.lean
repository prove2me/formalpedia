-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_det_submatrix_mul_eq_sum
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.det_submatrix_mul_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:16.3399+00:00
-- url     : https://prove2.me/theorems/109aa1c3-958a-4e67-9ac1-6543a1749041
-- title:
--   Height Descent Minors: det submatrix mul eq sum
-- statement:
--   The Height Descent Minors construction uses the det submatrix mul eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1426-L1441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1426-L1441

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.det_submatrix_mul_eq_sum {α β γ τ : Type} [Fintype β] [Fintype τ] [DecidableEq τ]
    (G : Matrix α β R) (P : Matrix β γ R) (f : τ → α) (g : τ → γ) :
    ((G * P).submatrix f g).det =
      ∑ r : τ → β, (∏ i, G (f i) (r i)) * (P.submatrix r g).det := by sorry
