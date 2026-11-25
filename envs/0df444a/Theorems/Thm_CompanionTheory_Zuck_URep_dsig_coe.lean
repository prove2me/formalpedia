-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_URep_dsig_coe
-- name    : CompanionTheory.Zuck.URep.dsig_coe
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:44:55.271822+00:00
-- url     : https://prove2.me/theorems/23357cd1-bec1-5a1e-9bf1-46acb86eeec8
-- title:
--   URep: dsig coe
-- statement:
--   The URep construction uses the dsig coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/IsSimpleFam.lean#L137-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/IsSimpleFam.lean#L137-L139

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

theorem CompanionTheory.Zuck.URep.dsig_coe (U : URep k r) {X : Mx k r} (hX : InLieHpk k r X) (v : U.R.smSub) :
    (U.dsig X v : U.R.H) = PI.UpqRep.dsig (k := k) (r := r) U.R.σ X v := by sorry
