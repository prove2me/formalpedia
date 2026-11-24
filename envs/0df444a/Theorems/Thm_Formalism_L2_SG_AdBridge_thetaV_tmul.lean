-- Prove2me | Theorems.Thm_Formalism_L2_SG_AdBridge_thetaV_tmul
-- name    : Formalism.L2.SG.AdBridge.thetaV_tmul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:41:28.459924+00:00
-- url     : https://prove2.me/theorems/7e8cf0f4-53d9-4e9d-9eb0-36ff2a8c6976
-- title:
--   Ad Bridge: theta V tmul
-- statement:
--   The Ad Bridge construction uses the theta V tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FundamentalEquivalence/AdBridge.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FundamentalEquivalence/AdBridge.lean#L42-L47

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
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
variable (I : AutInst)

theorem Formalism.L2.SG.AdBridge.thetaV_tmul (v : InfinitePlace I.F) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (x : I.E) :
    thetaV I v (a ⊗ₜ[I.F] x) = evV I v a * I.φ v x := by sorry
