-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_sigmaSimple_of
-- name    : Formalism.L2.Th1.F.sigmaSimple_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:00.316787+00:00
-- url     : https://prove2.me/theorems/0295e795-1d49-4f16-9b8a-5247617e89ca
-- title:
--   F: sigma Simple of
-- statement:
--   The F construction uses the sigma Simple of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaQuasi.lean#L253-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaQuasi.lean#L253-L272

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaQuasi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open PeriodLatticeBasisLemmas

theorem Formalism.L2.Th1.F.sigmaSimple_of (hq : SigmaQuasi) (he : SigmaEntire)
    (h0 : ∀ L : PeriodPair, deriv (wSigma L) 0 = 1) : SigmaSimple := by sorry
