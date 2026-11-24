-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_charpoly_theta_eq_prod
-- name    : Formalism.CohomologicalDescent.FrobeniusPeriodChange.charpoly_theta_eq_prod
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:54:31.425054+00:00
-- url     : https://prove2.me/theorems/a15747b5-35c6-4c00-9f47-7c651a964cd3
-- title:
--   Frobenius Period Change: charpoly theta eq prod
-- statement:
--   The Frobenius Period Change construction uses the charpoly theta eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L705-L724
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L705-L724

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

theorem Formalism.CohomologicalDescent.FrobeniusPeriodChange.charpoly_theta_eq_prod (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ)
    (hu : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c) (hN : LatW l W.N h u U') (i : ι) :
    (thetaOf (W.Gam i)).charpoly = ∏ j, (Polynomial.X -
      Polynomial.C (-W.red (algebraMap ℤ_[l] O c) * ((U' i j : ℤ) : F))) := by sorry
