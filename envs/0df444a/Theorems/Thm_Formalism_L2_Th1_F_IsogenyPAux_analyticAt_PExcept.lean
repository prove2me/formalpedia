-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_IsogenyPAux_analyticAt_PExcept
-- name    : Formalism.L2.Th1.F.IsogenyPAux.analyticAt_PExcept
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:47.82206+00:00
-- url     : https://prove2.me/theorems/acea1445-e5df-45aa-acb2-24f7b305b9e5
-- title:
--   Isogeny PAux: analytic At PExcept
-- statement:
--   The Isogeny PAux construction uses the analytic At PExcept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenyP.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenyP.lean#L23-L27

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Elliptic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenyP
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
open Formalism.L2.Th1.F.IsogenyPAux

theorem Formalism.L2.Th1.F.IsogenyPAux.analyticAt_PExcept (L : PeriodPair) (a z : ℂ) :
    AnalyticAt ℂ (fun w => L.weierstrassPExcept 0 (a * (w - z))) z := by sorry
