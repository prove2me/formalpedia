-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_dom_mem_nhds
-- name    : Formalism.L2.Th1.F.ThetaZeroTaylorLemmas.dom_mem_nhds
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:29:07.070212+00:00
-- url     : https://prove2.me/theorems/1c4c7cb3-db1d-4106-89a9-0bec6e16ae01
-- title:
--   Theta Zero Taylor Lemmas: dom mem nhds
-- statement:
--   The Theta Zero Taylor Lemmas construction uses the dom mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorEvenTheta.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorEvenTheta.lean#L46-L48

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

theorem Formalism.L2.Th1.F.ThetaZeroTaylorLemmas.dom_mem_nhds (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) :
    {z : ℂ | z + t ∉ L.lattice} ∈ 𝓝 (0 : ℂ) := by sorry
