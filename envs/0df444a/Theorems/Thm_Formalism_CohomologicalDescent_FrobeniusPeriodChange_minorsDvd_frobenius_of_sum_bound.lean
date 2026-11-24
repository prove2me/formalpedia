-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_minorsDvd_frobenius_of_sum_bound
-- name    : Formalism.CohomologicalDescent.FrobeniusPeriodChange.minorsDvd_frobenius_of_sum_bound
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:53:42.115241+00:00
-- url     : https://prove2.me/theorems/d35ef9ad-3565-4a4a-8f5e-593da24613ab
-- title:
--   Frobenius Period Change: minors Dvd frobenius of sum bound
-- statement:
--   The Frobenius Period Change construction uses the minors Dvd frobenius of sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L742-L750
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L742-L750

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]

theorem Formalism.CohomologicalDescent.FrobeniusPeriodChange.minorsDvd_frobenius_of_sum_bound (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (u : ℤ_[l]ˣ) (U' : ι → Fin n → ℤ)
    (hN : LatW l W.N h u U') (i : ι) (r S : ℕ)
    (hS : ∀ J : Finset (Fin n), J.card = r → (S : ℤ) ≤ ∑ j ∈ J, U' i j) :
    MinorsDvd ((X : F⟦X⟧) ^ S) r (W.Phi l σ i) := by sorry
