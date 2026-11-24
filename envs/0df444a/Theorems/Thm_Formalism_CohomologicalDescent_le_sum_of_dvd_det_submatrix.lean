-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_le_sum_of_dvd_det_submatrix
-- name    : Formalism.CohomologicalDescent.le_sum_of_dvd_det_submatrix
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:45:23.704392+00:00
-- url     : https://prove2.me/theorems/332fd0ce-fd6e-4f52-9190-da0663419e9f
-- title:
--   Cohomological Descent: le sum of dvd det submatrix
-- statement:
--   The Cohomological Descent construction uses the le sum of dvd det submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RegularCuspidalTrace.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RegularCuspidalTrace.lean#L12-L24

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWAssembled
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MinorValuationBoundHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeChainHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent

theorem Formalism.CohomologicalDescent.le_sum_of_dvd_det_submatrix {R : Type*} [CommRing R] [IsDomain R] (π : R) (hπ : Prime π) {t n : ℕ}
    (Φ : Matrix (Fin n) (Fin n) R) (b : Fin n → ℕ) (pos : Fin t → Fin n)
    (hinj : Function.Injective pos) (hpos : ∀ s j, b j = b (pos s) → j = pos s)
    (hΦ : Φ.BlockTriangular b) (al : Fin t → ℕ)
    (hdiag : ∀ s, ∃ u : Rˣ, Φ (pos s) (pos s) = (u : R) * π ^ al s) (c : ℕ)
    (hdvd : π ^ c ∣ (Φ.submatrix pos pos).det) : c ≤ ∑ s, al s := by sorry
