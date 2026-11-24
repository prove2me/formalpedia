-- Prove2me | Theorems.Thm_Formalism_L2_SG_AdBridge_bridge_apply_eq_of_comp
-- name    : Formalism.L2.SG.AdBridge.bridge_apply_eq_of_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:57:42.517671+00:00
-- url     : https://prove2.me/theorems/ef4c6e3a-5f78-4a2e-a6c2-c2175af1e135
-- title:
--   Ad Bridge: bridge apply eq of comp
-- statement:
--   The Ad Bridge construction uses the bridge apply eq of comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalPointsComparison/BridgeApplyEqOfComp.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalPointsComparison/BridgeApplyEqOfComp.lean#L30-L44

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

theorem Formalism.L2.SG.AdBridge.bridge_apply_eq_of_comp (I : AutInst) (e : I.GA ≃ₜ* HAd I) (he : IsBridge I e)
    (x : I.GA) (h : HAd I) (h1 : ∀ v, uMat (x.1 v) = ofHAInf I h v)
    (h2 : I.fmat x.2 = ofHAFin I h) : e x = h := by sorry
