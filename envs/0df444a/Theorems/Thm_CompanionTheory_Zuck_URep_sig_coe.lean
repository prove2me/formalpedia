-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_URep_sig_coe
-- name    : CompanionTheory.Zuck.URep.sig_coe
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:44:49.779102+00:00
-- url     : https://prove2.me/theorems/0e9b8990-68ea-5921-8a94-4e1149a98f52
-- title:
--   URep: sig coe
-- statement:
--   The URep construction uses the sig coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/IsSimpleFam.lean#L133-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/IsSimpleFam.lean#L133-L135

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPrAlt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_DSInfCharCap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open CompanionTheory CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
open PI.UpqRep (IsURepOn InLieHpk dsigW IsHCParam)
attribute [instance] FRep.fin FRep.dec
variable {k r : ℕ}

theorem CompanionTheory.Zuck.URep.sig_coe (U : URep k r) {g : Mx k r} (hg : g ∈ GG k r) (v : U.R.smSub) :
    (U.sig g v : U.R.H) = U.R.σ g v := by sorry
