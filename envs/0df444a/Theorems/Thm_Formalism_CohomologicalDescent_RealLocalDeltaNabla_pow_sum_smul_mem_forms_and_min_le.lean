-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_pow_sum_smul_mem_forms_and_min_le
-- name    : Formalism.CohomologicalDescent.RealLocalDeltaNabla.pow_sum_smul_mem_forms_and_min_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:09:15.606081+00:00
-- url     : https://prove2.me/theorems/34307e5b-b185-4856-9db0-819b80407af3
-- title:
--   Real Local Delta Nabla: pow sum smul mem forms and min le
-- statement:
--   The Real Local Delta Nabla construction uses the pow sum smul mem forms and min le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RealLocalDeltaNabla.lean#L218-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RealLocalDeltaNabla.lean#L218-L227

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
variable (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ) (hl : l.Prime)
  (hlO : ¬ IsUnit (l : O)) (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i)
  (ν : ∀ i, Fin (n i) → ℕ) (e : ι → ℕ) (he : ∀ i, InclZ (r i) (n i) (hn i) (ν i) l (e i))
include hl hlO he

theorem Formalism.CohomologicalDescent.RealLocalDeltaNabla.pow_sum_smul_mem_forms_and_min_le (G : Type) [Group G] (Γ K : Subgroup G)
    (ρK : Representation O K (Nabla O r n ν)) :
    (∀ f ∈ AMFK O Γ K ρK, (l : O) ^ (∑ i, e i) • f ∈ formsIn Γ K ρK (Delta O r n hn ν)) ∧
    sInf {J : ℕ | ∀ f ∈ AMFK O Γ K ρK, (l : O) ^ J • f ∈ formsIn Γ K ρK (Delta O r n hn ν)} ≤
      ∑ i, e i := by sorry
