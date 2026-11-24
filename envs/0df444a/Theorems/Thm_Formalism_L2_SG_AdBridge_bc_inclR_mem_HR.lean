-- Prove2me | Theorems.Thm_Formalism_L2_SG_AdBridge_bc_inclR_mem_HR
-- name    : Formalism.L2.SG.AdBridge.bc_inclR_mem_HR
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:56:52.351696+00:00
-- url     : https://prove2.me/theorems/d014dd61-5e91-4405-8dc3-d3f188ada0b7
-- title:
--   Ad Bridge: bc incl R mem HR
-- statement:
--   The Ad Bridge construction uses the bc incl R mem HR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalPointsComparison/BridgeApplyEqOfComp.lean#L54-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalPointsComparison/BridgeApplyEqOfComp.lean#L54-L66

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalPointsComparison_BridgeApplyEqOfComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.AdBridge
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)

theorem Formalism.L2.SG.AdBridge.bc_inclR_mem_HR (I : AutInst) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) :
    Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) γ ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := by sorry
