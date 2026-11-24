-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_injective_of_prime_to_units
-- name    : Formalism.CohomologicalDescent.RealLocalDeltaNabla.injective_of_prime_to_units
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:09:17.252201+00:00
-- url     : https://prove2.me/theorems/4dac9653-5cb0-47f4-ba5a-2e6c9d934042
-- title:
--   Real Local Delta Nabla: injective of prime to units
-- statement:
--   The Real Local Delta Nabla construction uses the injective of prime to units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RealLocalDeltaNabla.lean#L44-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RealLocalDeltaNabla.lean#L44-L56

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices

theorem Formalism.CohomologicalDescent.RealLocalDeltaNabla.injective_of_prime_to_units (R O : Type) [CommRing R] [CommRing O] [CharZero O] (φ : R →+* O) (l : ℕ)
    (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R))
    (hd : ∀ a : R, ∃ m : ℕ, ¬ l ∣ m ∧ ∃ z : ℤ, (m : R) * a = z) : Function.Injective φ := by sorry
