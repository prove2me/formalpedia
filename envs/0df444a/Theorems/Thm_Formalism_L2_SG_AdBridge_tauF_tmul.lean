-- Prove2me | Theorems.Thm_Formalism_L2_SG_AdBridge_tauF_tmul
-- name    : Formalism.L2.SG.AdBridge.tauF_tmul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:40:40.0928+00:00
-- url     : https://prove2.me/theorems/44be34ea-71f7-47c7-ad16-0ccb5235d3a8
-- title:
--   Ad Bridge: tau F tmul
-- statement:
--   The Ad Bridge construction uses the tau F tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FundamentalEquivalence/AdBridge.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FundamentalEquivalence/AdBridge.lean#L56-L61

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

theorem Formalism.L2.SG.AdBridge.tauF_tmul (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (x : I.E) :
    tauF I (a ⊗ₜ[I.F] x) = x ⊗ₜ[I.F] a.2 := by sorry
