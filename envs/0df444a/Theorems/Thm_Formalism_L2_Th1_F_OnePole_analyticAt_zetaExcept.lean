-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_OnePole_analyticAt_zetaExcept
-- name    : Formalism.L2.Th1.F.OnePole.analyticAt_zetaExcept
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:11.466266+00:00
-- url     : https://prove2.me/theorems/53cc6483-9538-4662-a41b-16b2ce30b206
-- title:
--   One Pole: analytic At zeta Except
-- statement:
--   The One Pole construction uses the analytic At zeta Except property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/OnePole.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/OnePole.lean#L36-L42

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_OnePole
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
open Formalism.L2.Th1.F.OnePole
open AnalyticIdentityTheoremsZetaFacts

theorem Formalism.L2.Th1.F.OnePole.analyticAt_zetaExcept (L : PeriodPair) : AnalyticAt ℂ (zetaExcept L 0) 0 := by sorry
