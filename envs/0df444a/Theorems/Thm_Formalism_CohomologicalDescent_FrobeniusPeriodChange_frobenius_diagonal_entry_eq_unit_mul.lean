-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_frobenius_diagonal_entry_eq_unit_mul
-- name    : Formalism.CohomologicalDescent.FrobeniusPeriodChange.frobenius_diagonal_entry_eq_unit_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:53:22.557796+00:00
-- url     : https://prove2.me/theorems/a9a97b50-e35e-4569-8022-9ff58236af88
-- title:
--   Frobenius Period Change: frobenius diagonal entry eq unit mul
-- statement:
--   The Frobenius Period Change construction uses the frobenius diagonal entry eq unit mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L752-L771
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L752-L771

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

theorem Formalism.CohomologicalDescent.FrobeniusPeriodChange.frobenius_diagonal_entry_eq_unit_mul (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ)
    (wt kap : ι → Fin t → ℤ) (hW : WInputs W σ l h u c U' wt kap) (i : ι) (s : Fin t) :
    0 ≤ (l : ℤ) * kap (σ i) s + wt i s - kap i s ∧
      ∃ u0 : (F⟦X⟧)ˣ, W.Phi l σ i (W.pos s) (W.pos s) =
        (u0 : F⟦X⟧) * X ^ ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat := by sorry
