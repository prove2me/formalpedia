-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_IsogenyPAux_analyticAt_P
-- name    : Formalism.L2.Th1.F.IsogenyPAux.analyticAt_P
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:55.411648+00:00
-- url     : https://prove2.me/theorems/090f71c0-0374-478e-8c0a-73383d845c5c
-- title:
--   Isogeny PAux: analytic At P
-- statement:
--   The Isogeny PAux construction uses the analytic At P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenyP.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenyP.lean#L18-L21

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

theorem Formalism.L2.Th1.F.IsogenyPAux.analyticAt_P (L : PeriodPair) (a b z : ℂ) (hz : a * z + b ∉ L.lattice) :
    AnalyticAt ℂ (fun w => L.weierstrassP (a * w + b)) z := by sorry
