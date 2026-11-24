-- Prove2me | Theorems.Thm_Formalism_L2_SG_AdBridge_sigR_inclR_star
-- name    : Formalism.L2.SG.AdBridge.sigR_inclR_star
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:57:00.490805+00:00
-- url     : https://prove2.me/theorems/b167a3eb-4719-4d99-afb9-803d42a1af0b
-- title:
--   Ad Bridge: sig R incl R star
-- statement:
--   The Ad Bridge construction uses the sig R incl R star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalPointsComparison/BridgeApplyEqOfComp.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalPointsComparison/BridgeApplyEqOfComp.lean#L46-L52

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

theorem Formalism.L2.SG.AdBridge.sigR_inclR_star (I : AutInst) (y : I.E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig
              (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) y) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (starRingEnd I.E y) := by sorry
