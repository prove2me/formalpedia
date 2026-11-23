-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_submatrix_det_not_dvd_of_mul_eq
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.exists_submatrix_det_not_dvd_of_mul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:13.833977+00:00
-- url     : https://prove2.me/theorems/3fd353d1-33b2-443b-8686-7b01ee3fdac5
-- title:
--   Height Descent Minors: exists submatrix det not dvd of mul eq
-- statement:
--   The Height Descent Minors construction uses the exists submatrix det not dvd of mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1486-L1498
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1486-L1498

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.exists_submatrix_det_not_dvd_of_mul_eq {ι τ : Type} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]
    (x : R) (h : ℕ) (M M' : Matrix ι ι R) (e : τ → ι) (he : Function.Injective e)
    (hM : M * M' = (x ^ h) • (1 : Matrix ι ι R))
    (hx : ¬ x ^ (Fintype.card τ * h + 1) ∣ x ^ (Fintype.card τ * h)) :
    ∃ f g : τ → ι, ¬ x ^ (Fintype.card τ * h + 1) ∣ (M.submatrix f g).det := by sorry
