-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_hasDerivAt_v
-- name    : Formalism.L2.Th1.F.ThetaZeroTaylorLemmas.hasDerivAt_v
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:33:13.551212+00:00
-- url     : https://prove2.me/theorems/2c1a2234-76aa-4379-8b7a-272f7feb29e1
-- title:
--   Theta Zero Taylor Lemmas: has Deriv At v
-- statement:
--   The Theta Zero Taylor Lemmas construction uses the has Deriv At v property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorEvenTheta.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorEvenTheta.lean#L50-L56

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorEvenTheta
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

theorem Formalism.L2.Th1.F.ThetaZeroTaylorLemmas.hasDerivAt_v (L : PeriodPair) {t z : ℂ} (h : z + t ∉ L.lattice) :
    HasDerivAt (v L t) (-(L.weierstrassP (z + t)) - s2 L) z := by sorry
