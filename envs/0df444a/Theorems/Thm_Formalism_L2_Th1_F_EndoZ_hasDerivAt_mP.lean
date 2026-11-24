-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_EndoZ_hasDerivAt_mP
-- name    : Formalism.L2.Th1.F.EndoZ.hasDerivAt_mP
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:33:34.464813+00:00
-- url     : https://prove2.me/theorems/e91622a2-4e16-482c-89aa-ce2f0bed3035
-- title:
--   Endo Z: has Deriv At m P
-- statement:
--   The Endo Z construction uses the has Deriv At m P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IntegerEndomorphismInstance.lean#L230-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IntegerEndomorphismInstance.lean#L230-L243

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EndoZ
open PowerSeries TaylorWp

theorem Formalism.L2.Th1.F.EndoZ.hasDerivAt_mP (L : PeriodPair) {P w : ℂ} (hw : w ∈ U L P) :
    HasDerivAt (mP L P) (2 * L.weierstrassPExcept 0 w - L.weierstrassP (w + P)
      - L.weierstrassP (w - P)) w := by sorry
