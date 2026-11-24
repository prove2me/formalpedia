-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_pow_sum_smul_mem_localised_forms
-- name    : Formalism.CohomologicalDescent.RealLocalDeltaNabla.pow_sum_smul_mem_localised_forms
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:08:51.233004+00:00
-- url     : https://prove2.me/theorems/287d21a8-b423-4435-b5df-b1de7ef710b7
-- title:
--   Real Local Delta Nabla: pow sum smul mem localised forms
-- statement:
--   The Real Local Delta Nabla construction uses the pow sum smul mem localised forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RealLocalDeltaNabla.lean#L229-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RealLocalDeltaNabla.lean#L229-L251

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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

theorem Formalism.CohomologicalDescent.RealLocalDeltaNabla.pow_sum_smul_mem_localised_forms (G : Type) [Group G] (Γ K : Subgroup G)
    (ρK : Representation O K (Nabla O r n ν))
    (T : Type) [CommRing T] [Algebra O T] [Module T (AMFK O Γ K ρK)]
    [IsScalarTower O T (AMFK O Γ K ρK)] (S : Submonoid T) :
    (∀ y : LocalizedModule S (AMFK O Γ K ρK),
        (algebraMap O T (l : O)) ^ (∑ i, e i) • y ∈
          locSet S {x : AMFK O Γ K ρK | (x : G → Nabla O r n ν) ∈
            formsIn Γ K ρK (Delta O r n hn ν)}) ∧
    sInf {J : ℕ | ∀ y : LocalizedModule S (AMFK O Γ K ρK),
        (algebraMap O T (l : O)) ^ J • y ∈
          locSet S {x : AMFK O Γ K ρK | (x : G → Nabla O r n ν) ∈
            formsIn Γ K ρK (Delta O r n hn ν)}} ≤ ∑ i, e i := by sorry
