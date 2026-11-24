-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_analyticAt_v
-- name    : Formalism.L2.Th1.F.ThetaZeroTaylorLemmas.analyticAt_v
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:30:05.64402+00:00
-- url     : https://prove2.me/theorems/44683c3a-fc7a-4807-a2d6-1188316a0279
-- title:
--   Theta Zero Taylor Lemmas: analytic At v
-- statement:
--   The Theta Zero Taylor Lemmas construction uses the analytic At v property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorEvenTheta.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorEvenTheta.lean#L58-L60

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorEvenTheta
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_analyticAt_v

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.ThetaZeroTaylorLemmas

theorem Formalism.L2.Th1.F.ThetaZeroTaylorLemmas.analyticAt_v (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) : AnalyticAt ℂ (v L t) 0 := by sorry
