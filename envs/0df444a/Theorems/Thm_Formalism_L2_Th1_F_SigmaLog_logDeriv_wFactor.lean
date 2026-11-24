-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_SigmaLog_logDeriv_wFactor
-- name    : Formalism.L2.Th1.F.SigmaLog.logDeriv_wFactor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:50.579514+00:00
-- url     : https://prove2.me/theorems/1297cf0e-07c6-4de6-a908-7c8f94918248
-- title:
--   Sigma Log: log Deriv w Factor
-- statement:
--   The Sigma Log construction uses the log Deriv w Factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaLog.lean#L34-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaLog.lean#L34-L50

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaLog

theorem Formalism.L2.Th1.F.SigmaLog.logDeriv_wFactor {l z : ℂ} (h : z ≠ l) :
    logDeriv (wFactor l) z
      = (1 / (z - l) + 1 / l + z / l ^ 2) - (if l = 0 then 1 / z else 0) := by sorry
